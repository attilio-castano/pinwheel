import Pinwheel.Hardware.Memory.ByteAccess

/-! The first RV32I execution environment's pure address decoder. Effective
addresses have already wrapped to 32 bits before this layer. All interval and
footprint checks use unbounded naturals; local address narrowing is justified
only after successful routing. MMIO register holes and directions are checked
by the peripheral layer, never by a RAM read-modify-write adapter. -/
namespace Pinwheel.Hardware.Processor.AddressMap

open Memory.ByteAccess

inductive Region where
  | rom | ram | gpio | timer | uart
  deriving DecidableEq, Repr

instance (p : Region → Prop) [∀ r, Decidable (p r)] : Decidable (∀ r, p r) :=
  decidable_of_iff (p .rom ∧ p .ram ∧ p .gpio ∧ p .timer ∧ p .uart) (by
    constructor
    · intro h r
      cases r <;> simp_all
    · intro h
      exact ⟨h _, h _, h _, h _, h _⟩)

def Region.wordWidth (romWidth ramWidth : Nat) : Region → Nat
  | .rom => romWidth
  | .ram => ramWidth
  | .gpio | .timer | .uart => 6

structure Config (romWidth ramWidth : Nat) where
  ramBase : BitVec 32
  gpioBase : BitVec 32
  timerBase : BitVec 32
  uartBase : BitVec 32
  deriving Repr

def Config.base (c : Config romWidth ramWidth) : Region → Nat
  | .rom => 0
  | .ram => c.ramBase.toNat
  | .gpio => c.gpioBase.toNat
  | .timer => c.timerBase.toNat
  | .uart => c.uartBase.toNat

def capacity (romWidth ramWidth : Nat) (r : Region) : Nat :=
  4 * 2 ^ r.wordWidth romWidth ramWidth

def Config.limit (c : Config romWidth ramWidth) (r : Region) : Nat :=
  c.base r + capacity romWidth ramWidth r

def Config.Separate (c : Config romWidth ramWidth) (r s : Region) : Prop :=
  c.limit r ≤ c.base s ∨ c.limit s ≤ c.base r

instance (c : Config romWidth ramWidth) (r s : Region) : Decidable (c.Separate r s) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Config.Valid (c : Config romWidth ramWidth) : Prop :=
  (∀ r, c.base r % 4 = 0 ∧ 0 < capacity romWidth ramWidth r ∧ c.limit r ≤ 2^32) ∧
  (∀ r s, r ≠ s → c.Separate r s)

instance (c : Config romWidth ramWidth) : Decidable c.Valid :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

/-- Routing accepts only a checked layout; callers cannot omit layout validity. -/
structure Layout (romWidth ramWidth : Nat) where
  config : Config romWidth ramWidth
  valid : config.Valid

def check (c : Config romWidth ramWidth) : Option (Layout romWidth ramWidth) :=
  if h : c.Valid then some ⟨c, h⟩ else none

inductive Kind where
  | fetch | load | store
  deriving DecidableEq, Repr

structure Access where
  kind : Kind
  size : Size
  address : BitVec 32
  deriving DecidableEq, Repr

/-- Fetch always requires four-byte alignment, including a malformed request
with a non-word size. Such a request then fails the permission check. -/
def Access.bytes (a : Access) : Nat :=
  if a.kind = .fetch then 4 else a.size.bytes

def Access.Aligned (a : Access) : Prop := a.address.toNat % a.bytes = 0

def Contains (l : Layout romWidth ramWidth) (r : Region) (a : Access) : Prop :=
  l.config.base r ≤ a.address.toNat ∧ a.address.toNat + a.bytes ≤ l.config.limit r

def Permitted (r : Region) (a : Access) : Prop :=
  match r, a.kind with
  | .rom, .fetch => a.size = .word
  | .rom, .load => True
  | .rom, .store => False
  | .ram, .fetch => False
  | .ram, .load | .ram, .store => True
  | _, .fetch => False
  | _, .load | _, .store => a.size = .word

instance (a : Access) : Decidable a.Aligned := inferInstanceAs (Decidable (_ = _))
instance (l : Layout romWidth ramWidth) (r : Region) (a : Access) :
    Decidable (Contains l r a) := inferInstanceAs (Decidable (_ ∧ _))
instance (r : Region) (a : Access) : Decidable (Permitted r a) := by
  unfold Permitted
  cases r <;> cases a.kind <;> infer_instance

inductive Fault where
  | misaligned | access
  deriving DecidableEq, Repr

/-- A successful decoder result carries the exact admission guarantees. Its
local word index is computed as a natural before any bitvector conversion. -/
structure Hit (l : Layout romWidth ramWidth) (a : Access) where
  region : Region
  aligned : a.Aligned
  contained : Contains l region a
  permitted : Permitted region a

private def admit (l : Layout romWidth ramWidth) (a : Access) (ha : a.Aligned)
    (r : Region) (hc : Contains l r a) : Except Fault (Hit l a) :=
  if hp : Permitted r a then .ok ⟨r, ha, hc, hp⟩ else .error .access

def route (l : Layout romWidth ramWidth) (a : Access) : Except Fault (Hit l a) :=
  if ha : a.Aligned then
    if h : Contains l .rom a then admit l a ha .rom h
    else if h : Contains l .ram a then admit l a ha .ram h
    else if h : Contains l .gpio a then admit l a ha .gpio h
    else if h : Contains l .timer a then admit l a ha .timer h
    else if h : Contains l .uart a then admit l a ha .uart h
    else .error .access
  else .error .misaligned

variable {romWidth ramWidth : Nat} {l : Layout romWidth ramWidth} {a : Access}

def Hit.relative (h : Hit l a) : Nat := a.address.toNat - l.config.base h.region
def Hit.wordIndex (h : Hit l a) : Nat := h.relative / 4
def Hit.byteOffset (h : Hit l a) : Nat := h.relative % 4

theorem Access.bytes_pos (a : Access) : 0 < a.bytes := by
  cases hk : a.kind <;> cases hz : a.size <;> simp [Access.bytes, Size.bytes, hk, hz]

theorem contains_unique (l : Layout romWidth ramWidth) (a : Access) (r s : Region)
    (hr : Contains l r a) (hs : Contains l s a) : r = s := by
  by_cases same : r = s
  · exact same
  have separate := l.valid.2 r s same
  have positive := a.bytes_pos
  simp only [Config.Separate, Contains] at *
  omega

theorem Hit.wordIndex_lt (h : Hit l a) :
    h.wordIndex < 2 ^ h.region.wordWidth romWidth ramWidth := by
  have contained := h.contained
  have positive := a.bytes_pos
  simp only [Contains, Config.limit, capacity, Hit.wordIndex, Hit.relative] at *
  omega

theorem Hit.reconstruct (h : Hit l a) :
    a.address.toNat = l.config.base h.region + 4 * h.wordIndex + h.byteOffset := by
  have contained := h.contained.1
  simp only [Hit.wordIndex, Hit.byteOffset, Hit.relative]
  omega

theorem Hit.contains_iff (h : Hit l a) (r : Region) :
    Contains l r a ↔ r = h.region := by
  constructor
  · exact fun hc => contains_unique l a r h.region hc h.contained
  · intro same
    simpa [same] using h.contained

theorem Hit.unique (h k : Hit l a) : h = k := by
  have same := contains_unique l a h.region k.region h.contained k.contained
  cases h
  cases k
  cases same
  rfl

theorem route_complete (h : Hit l a) : route l a = .ok h := by
  have hc := h.contains_iff
  simp only [route, h.aligned, dif_pos, hc]
  cases h with
  | mk region aligned contained permitted =>
    cases region <;> simp_all [admit]

theorem route_success_iff (l : Layout romWidth ramWidth) (a : Access) :
    (∃ h, route l a = .ok h) ↔
      a.Aligned ∧ ∃ r, Contains l r a ∧ Permitted r a := by
  constructor
  · rintro ⟨h, _⟩
    exact ⟨h.aligned, h.region, h.contained, h.permitted⟩
  · rintro ⟨ha, r, hc, hp⟩
    exact ⟨⟨r, ha, hc, hp⟩, route_complete _⟩

theorem route_misaligned (l : Layout romWidth ramWidth) (a : Access)
    (ha : ¬a.Aligned) : route l a = .error .misaligned := by
  simp [route, ha]

theorem route_misaligned_iff (l : Layout romWidth ramWidth) (a : Access) :
    route l a = .error .misaligned ↔ ¬a.Aligned := by
  constructor
  · intro h ha
    simp [route, admit, ha] at h
    repeat' split at h
    all_goals simp_all
  · exact route_misaligned l a

theorem route_access_iff (l : Layout romWidth ramWidth) (a : Access) :
    route l a = .error .access ↔
      a.Aligned ∧ ¬∃ r, Contains l r a ∧ Permitted r a := by
  constructor
  · intro hr
    have ha : a.Aligned := by
      by_cases ha : a.Aligned
      · exact ha
      · simp [route_misaligned l a ha] at hr
    refine ⟨ha, ?_⟩
    rintro ⟨r, hc, hp⟩
    have success := route_complete (⟨r, ha, hc, hp⟩ : Hit l a)
    simp [hr] at success
  · rintro ⟨ha, absent⟩
    cases hr : route l a with
    | ok h => exact False.elim (absent ⟨h.region, h.contained, h.permitted⟩)
    | error f =>
      cases f
      · exact False.elim ((route_misaligned_iff l a).mp hr ha)
      · rfl

theorem Hit.offset_lt (h : Hit l a) : h.byteOffset < 4 := Nat.mod_lt _ (by decide)

theorem Hit.offset_eq_address (h : Hit l a) : h.byteOffset = a.address.toNat % 4 := by
  have lower := h.contained.1
  have aligned := (l.valid.1 h.region).1
  simp only [Hit.byteOffset, Hit.relative]
  omega

theorem Hit.local_aligned (h : Hit l a) : h.byteOffset % a.bytes = 0 := by
  have aligned := h.aligned
  rw [h.offset_eq_address]
  cases hk : a.kind <;> cases hz : a.size <;>
    simp [Access.Aligned, Access.bytes, Size.bytes, hk, hz] at *
  all_goals assumption

theorem Hit.local_footprint (h : Hit l a) : h.byteOffset + a.bytes ≤ 4 := by
  have bound := h.offset_lt
  have aligned := h.local_aligned
  cases hk : a.kind <;> cases hz : a.size <;>
    simp [Access.bytes, Size.bytes, hk, hz] at *
  all_goals omega

/-- Every byte is inside the selected region in widened arithmetic. -/
theorem Hit.byte_bounds (h : Hit l a) (j : Nat) (hj : j < a.bytes) :
    l.config.base h.region ≤ a.address.toNat + j ∧
    a.address.toNat + j < l.config.limit h.region := by
  have contained := h.contained
  simp only [Contains] at contained
  omega

theorem Hit.no_wrap (h : Hit l a) : a.address.toNat + a.bytes ≤ 2^32 :=
  Nat.le_trans h.contained.2 (l.valid.1 h.region).2.2

theorem Hit.region_disjoint (h : Hit l a) (r : Region) (different : r ≠ h.region) :
    ¬Contains l r a := by
  simpa [h.contains_iff] using different

theorem Hit.fetch_rom (h : Hit l a) (hf : a.kind = .fetch) :
    h.region = .rom ∧ a.size = .word := by
  have permitted := h.permitted
  cases hr : h.region <;> simp_all [Permitted]

theorem Hit.store_not_rom (h : Hit l a) (hs : a.kind = .store) : h.region ≠ .rom := by
  intro hr
  have permitted := h.permitted
  simp [Permitted, hr, hs] at permitted

theorem Hit.mmio_word (h : Hit l a)
    (mmio : h.region = .gpio ∨ h.region = .timer ∨ h.region = .uart) :
    a.kind ≠ .fetch ∧ a.size = .word := by
  have permitted := h.permitted
  rcases mmio with hr | hr | hr <;> cases hk : a.kind <;> simp_all [Permitted]

theorem Hit.bytes_eq_size (h : Hit l a) : a.bytes = a.size.bytes := by
  by_cases hf : a.kind = .fetch
  · simp [Access.bytes, hf, (h.fetch_rom hf).2, Size.bytes]
  · simp [Access.bytes, hf]

/-- This narrowing is available only after the exact natural bound is proved. -/
def Hit.wordAddress (h : Hit l a) : BitVec (h.region.wordWidth romWidth ramWidth) :=
  BitVec.ofNat _ h.wordIndex

def Hit.offset (h : Hit l a) : BitVec 2 := BitVec.ofNat 2 h.byteOffset

@[simp] theorem Hit.wordAddress_toNat (h : Hit l a) : h.wordAddress.toNat = h.wordIndex := by
  simp [Hit.wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.wordIndex_lt]

@[simp] theorem Hit.offset_toNat (h : Hit l a) : h.offset.toNat = h.byteOffset := by
  simp [Hit.offset, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.offset_lt]

theorem Hit.byteAccess_aligned (h : Hit l a) : Memory.ByteAccess.Aligned a.size h.offset := by
  simpa only [Memory.ByteAccess.Aligned, h.offset_toNat, h.bytes_eq_size] using h.local_aligned

theorem Hit.byteAccess_fits (h : Hit l a) : h.offset.toNat + a.size.bytes ≤ 4 := by
  simpa only [h.offset_toNat, h.bytes_eq_size] using h.local_footprint

theorem Hit.narrow_reconstruct (h : Hit l a) :
    a.address.toNat = l.config.base h.region + 4 * h.wordAddress.toNat + h.offset.toNat := by
  simpa using h.reconstruct

theorem Hit.no_alias {b : Access} (h : Hit l a) (k : Hit l b)
    (region : h.region = k.region) (word : h.wordIndex = k.wordIndex)
    (offset : h.byteOffset = k.byteOffset) : a.address = b.address := by
  apply BitVec.eq_of_toNat_eq
  rw [h.reconstruct, k.reconstruct, region, word, offset]

theorem Hit.no_narrow_alias {b : Access} (h : Hit l a) (k : Hit l b)
    (region : h.region = k.region) (word : h.wordAddress.toNat = k.wordAddress.toNat)
    (offset : h.offset = k.offset) : a.address = b.address := by
  apply h.no_alias k region
  · simpa using word
  · simpa using congrArg BitVec.toNat offset

theorem check_isSome (c : Config romWidth ramWidth) : (check c).isSome = decide c.Valid := by
  by_cases hc : c.Valid <;> simp [check, hc]

def defaultConfig : Config 10 10 :=
  ⟨0x00010000, 0x40000000, 0x40000100, 0x40000200⟩

theorem defaultConfig_valid : defaultConfig.Valid := by decide +kernel

def defaultLayout : Layout 10 10 := ⟨defaultConfig, defaultConfig_valid⟩

end Pinwheel.Hardware.Processor.AddressMap
