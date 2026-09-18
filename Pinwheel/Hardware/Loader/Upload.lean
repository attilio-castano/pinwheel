import Pinwheel.Hardware.Loader.Delivery

/-! The upload theorem.

A host loads a program by telling the machine: begin, then 322 words, then
commit. `upload_loads` says what that does, whatever the spacing: if the engine
is not running and the consumed history delivers exactly those commands among
quiet edges, the machine ends with the other bank selected and valid, that bank
holding exactly the pushed words register by register (`imageOf`), the bank that
was active untouched, and the engine stopped with the new image's idle pins.

Pushes pass an admission predicate first (`admitted`), so the same theorem
covers the machine itself (every word admitted) and the reference the small
dense backends refine (the capacity check), which is what a chip runs. -/
namespace Pinwheel.Hardware.Loader.Machine

/-! ### The machine behind an admission check on pushes -/

/-- A push whose word `A` refuses at the cursor becomes a rejection. -/
def admitted (A : BitVec 9 → BitVec 64 → Bool) (i : Inputs) (s : State) : Inputs :=
  {i with command := if i.command == 2 && !A s.control.cursor i.data then 6 else i.command}

def stepWith (A : BitVec 9 → BitVec 64 → Bool) (i : Inputs) (s : State) : State :=
  next (admitted A i s) s

def runWith (A : BitVec 9 → BitVec 64 → Bool) (s : State) : List Inputs → State
  | [] => s
  | i :: rest => runWith A (stepWith A i s) rest

theorem runWith_append (A : BitVec 9 → BitVec 64 → Bool) (s : State) (a b : List Inputs) :
    runWith A s (a ++ b) = runWith A (runWith A s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih _

/-- Admitting everything is the machine itself. -/
theorem admitted_all (i : Inputs) (s : State) : admitted (fun _ _ => true) i s = i := by
  simp [admitted]

theorem admitted_of_command (A : BitVec 9 → BitVec 64 → Bool) (i : Inputs) (s : State)
    (h : (i.command == 2) = false) : admitted A i s = i := by
  unfold admitted
  rw [h]
  rfl

theorem admitted_of_accept (A : BitVec 9 → BitVec 64 → Bool) (i : Inputs) (s : State)
    (h : A s.control.cursor i.data = true) : admitted A i s = i := by
  simp [admitted, h]

/-- What the host says to load the words `ws`: begin, a push per word, commit. The
words that accompany begin and commit are ignored. -/
def uploadCommands (ws : List (BitVec 64)) (d₀ d₁ : BitVec 64) : List (BitVec 3 × BitVec 64) :=
  (1, d₀) :: (ws.map (fun w => ((2 : BitVec 3), w)) ++ [(3, d₁)])

/-- Every pushed word of a delivered history is one of the commands' words. -/
theorem Delivers.pushes {h : List Inputs} {cs : List (BitVec 3 × BitVec 64)} (hd : Delivers h cs)
    (R : BitVec 64 → Prop) (hR : ∀ d, ((2 : BitVec 3), d) ∈ cs → R d) :
    ∀ m ∈ h, m.command = 2 → R m.data := by
  induction hd with
  | nil => intro m hm; cases hm
  | quiet hq _ ih =>
    intro m hm hc
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [hq.2.2] at hc
      exact absurd hc (by decide)
    · exact ih hR m hm hc
  | @command m' h' c d cs' hcar _ ih =>
    intro m hm hc
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨_, _, hcmd, hdata⟩ := hcar
      rw [hdata]
      apply hR
      have hc2 : c = 2 := by
        cases h7 : (c != 7)
        · rw [h7] at hcmd
          have h0 : m.command = 0 := hcmd
          rw [h0] at hc
          exact absurd hc (by decide)
        · rw [h7] at hcmd
          have hcc : m.command = c := hcmd
          rw [hcc] at hc
          exact hc
      rw [hc2]
      exact List.mem_cons_self ..
    · exact ih (fun d hd => hR d (List.mem_cons_of_mem _ hd)) m hm hc

/-! ### The image a word list leaves -/

/-- Each store register holds the low bits of the word pushed at its offset. -/
def imageOf (ws : List (BitVec 64)) : Store.Image :=
  fun {w} r => (ws.getD (Store.offset r).toNat 0).extractLsb' 0 w

theorem offset_lt : {w : Nat} → (r : Store.Register w) → (Store.offset r).toNat < 322
  | _, .word k => by
    have := k.isLt
    simp only [Store.offset, BitVec.toNat_ofNat]
    omega
  | _, .index k => by
    have := k.isLt
    simp only [Store.offset, BitVec.toNat_ofNat]
    omega
  | _, .idle => by decide
  | _, .last => by decide

/-! ### One edge at a time, with the engine stopped -/

/-- Nothing but a start sets a stopped engine running. -/
theorem idle_next (i : Inputs) (s : State) (hidle : Reactive.runningValue s.core = false)
    (h5 : (i.command == 5) = false) : Reactive.runningValue (next i s).core = false := by
  have hstart : (schedulerInput i s).start = false := by
    show (Loader.enabled (controlInput i s) && (i.command == 5) && s.control.valid) = false
    rw [h5, Bool.and_false, Bool.false_and]
  simp only [next, Reactive.stepValue, hidle, hstart, Bool.false_eq_true, if_false]
  split
  · rfl
  · exact hidle

/-- A quiet edge with the engine stopped changes neither the loader nor a bank;
with a committed image it changes nothing at all. -/
theorem quiet_next (i : Inputs) (s : State) (hq : Quiet i)
    (hidle : Reactive.runningValue s.core = false) :
    (next i s).control = s.control ∧ (next i s).memory = s.memory ∧
      Reactive.runningValue (next i s).core = false ∧
      (s.control.valid = true → (next i s).core = s.core) := by
  obtain ⟨hi, hr, hc⟩ := hq
  have hcontrol : Loader.next (controlInput i s) s.control = s.control := by
    simp [Loader.next, controlInput, hi, hr, hc, Loader.commit, Loader.push, hidle]
  have hpush : Loader.push (controlInput i s) s.control = false := by
    simp [Loader.push, controlInput, hc]
  refine ⟨hcontrol, ?_, idle_next i s hidle (by rw [hc]; rfl), ?_⟩
  · funext b
    simp only [next, memoryInput, hpush, Bool.false_and]
    funext w r
    simp [Store.tick]
  · intro hv
    have hcommit : committing i s = false := by
      simp [committing, Loader.commit, controlInput, hc]
    have hreset : (schedulerInput i s).reset = false := by
      simp [schedulerInput, baseInput, hi, hr, hv, hcommit]
    have hstart : (schedulerInput i s).start = false := by
      simp [schedulerInput, baseInput, Loader.start, controlInput, hc]
    simp only [next, Reactive.stepValue, hreset, hidle, hstart, Bool.false_eq_true, if_false]

theorem carries_plain {i : Inputs} {c : BitVec 3} {d : BitVec 64} (h : Carries i c d)
    (hc : (c == 7) = false) : i.init = false ∧ i.reset = false ∧ i.command = c ∧ i.data = d := by
  obtain ⟨hi, hr, hcmd, hd⟩ := h
  have hne : (c != 7) = true := by
    unfold bne
    rw [hc]
    rfl
  rw [hc] at hr
  rw [hne] at hcmd
  exact ⟨hi, hr, hcmd, hd⟩

/-- Begin opens an upload at cursor zero and touches nothing else. -/
theorem begin_next (i : Inputs) (s : State) (d : BitVec 64) (hc : Carries i 1 d)
    (hidle : Reactive.runningValue s.core = false) :
    (next i s).control = {s.control with pending := true, cursor := 0} ∧
      (next i s).memory = s.memory ∧ Reactive.runningValue (next i s).core = false := by
  obtain ⟨hi, hr, hcmd, _⟩ := carries_plain hc (by decide)
  have hcontrol : Loader.next (controlInput i s) s.control =
      {s.control with pending := true, cursor := 0} := by
    simp [Loader.next, controlInput, hi, hr, hcmd, hidle]
  have hpush : Loader.push (controlInput i s) s.control = false := by
    simp [Loader.push, controlInput, hcmd]
  refine ⟨hcontrol, ?_, idle_next i s hidle (by rw [hcmd]; rfl)⟩
  funext b
  simp only [next, memoryInput, hpush, Bool.false_and]
  funext w r
  simp [Store.tick]

/-- An accepted push writes the word at the cursor in the staging bank and
advances the cursor; the active bank and the engine are untouched. -/
theorem pushed_next (i : Inputs) (s : State) (word : BitVec 64) (hc : Carries i 2 word)
    (hidle : Reactive.runningValue s.core = false) (hp : s.control.pending = true)
    (hk : s.control.cursor.toNat < 322) (hg : goodWord s.control.cursor word = true) :
    (next i s).control = {s.control with cursor := s.control.cursor - 511} ∧
      (∀ {w : Nat} (r : Store.Register w),
        (next i s).memory s.control.active r = s.memory s.control.active r) ∧
      (∀ {w : Nat} (r : Store.Register w), (next i s).memory (!s.control.active) r =
        Store.tick ⟨true, s.control.cursor, word, 0⟩ (s.memory (!s.control.active)) r) ∧
      Reactive.runningValue (next i s).core = false := by
  obtain ⟨hi, hr, hcmd, hd⟩ := carries_plain hc (by decide)
  have hpush : Loader.push (controlInput i s) s.control = true := by
    simp [Loader.push, Loader.enabled, controlInput, hi, hr, hcmd, hd, hidle, hp, hk, hg]
  have hb : ((!s.control.active) != s.control.active) = true := by
    cases s.control.active <;> rfl
  refine ⟨Loader.push_next _ _ hpush, fun r => ?_, fun r => ?_, idle_next i s hidle (by rw [hcmd]; rfl)⟩
  · simp only [next, memoryInput, hpush, Bool.true_and, bne_self_eq_false]
    simp [Store.tick]
  · simp only [next, memoryInput, hpush, Bool.true_and, hb, hd]

/-- A commit with the upload complete. -/
theorem complete_commits (i : Inputs) (s : State) (d : BitVec 64) (hc : Carries i 3 d)
    (hidle : Reactive.runningValue s.core = false) (hp : s.control.pending = true)
    (hk : s.control.cursor.toNat = 322) : committing i s = true := by
  obtain ⟨hi, hr, hcmd, _⟩ := carries_plain hc (by decide)
  have hcursor : s.control.cursor = 322 := BitVec.eq_of_toNat_eq (by rw [hk]; rfl)
  simp [committing, Loader.commit, Loader.enabled, controlInput, hi, hr, hcmd, hidle, hp, hcursor]

/-! ### The upload -/

/-- Part way through: `k` words staged in the bank that is not active. -/
structure Staging (ws : List (BitVec 64)) (k : Nat) (bank : Bool) (old : Store.Image) (s : State) :
    Prop where
  active : s.control.active = bank
  pending : s.control.pending = true
  cursor : s.control.cursor.toNat = k
  idle : Reactive.runningValue s.core = false
  staged : ∀ {w : Nat} (r : Store.Register w), (Store.offset r).toNat < k →
    s.memory (!bank) r = imageOf ws r
  kept : ∀ {w : Nat} (r : Store.Register w), s.memory bank r = old r

/-- Done: the other bank selected and valid, holding the words; the old bank as
it was; the engine stopped with the new image's idle pins. -/
structure Loaded (ws : List (BitVec 64)) (bank : Bool) (old : Store.Image) (s : State) : Prop where
  control : s.control = ⟨!bank, true, false, 0⟩
  image : ∀ {w : Nat} (r : Store.Register w), s.memory (!bank) r = imageOf ws r
  kept : ∀ {w : Nat} (r : Store.Register w), s.memory bank r = old r
  core : s.core = ⟨0, 0, 0, 0,
    ⟨(imageOf ws .idle).extractLsb' 0 3, (imageOf ws .idle).extractLsb' 3 3⟩,
    Vector.replicate 16 false⟩

theorem Loaded.idle {ws : List (BitVec 64)} {bank : Bool} {old : Store.Image} {s : State}
    (h : Loaded ws bank old s) : Reactive.runningValue s.core = false := by
  rw [h.core]
  rfl

variable (A : BitVec 9 → BitVec 64 → Bool)

theorem quiet_command {i : Inputs} (hq : Quiet i) : (i.command == 2) = false := by
  rw [hq.2.2]
  rfl

theorem staging_quiet {ws : List (BitVec 64)} {k : Nat} {bank : Bool} {old : Store.Image}
    {s : State} (h : Staging ws k bank old s) (i : Inputs) (hq : Quiet i) :
    Staging ws k bank old (stepWith A i s) := by
  unfold stepWith
  rw [admitted_of_command A i s (quiet_command hq)]
  obtain ⟨hcontrol, hmemory, hidle, _⟩ := quiet_next i s hq h.idle
  exact ⟨by rw [hcontrol]; exact h.active, by rw [hcontrol]; exact h.pending,
    by rw [hcontrol]; exact h.cursor, hidle, fun r hr => by rw [hmemory]; exact h.staged r hr,
    fun r => by rw [hmemory]; exact h.kept r⟩

theorem loaded_quiet {ws : List (BitVec 64)} {bank : Bool} {old : Store.Image} {s : State}
    (h : Loaded ws bank old s) (i : Inputs) (hq : Quiet i) : Loaded ws bank old (stepWith A i s) := by
  unfold stepWith
  rw [admitted_of_command A i s (quiet_command hq)]
  obtain ⟨hcontrol, hmemory, _, hcore⟩ := quiet_next i s hq h.idle
  have hvalid : s.control.valid = true := by rw [h.control]
  exact ⟨by rw [hcontrol]; exact h.control, fun r => by rw [hmemory]; exact h.image r,
    fun r => by rw [hmemory]; exact h.kept r, by rw [hcore hvalid]; exact h.core⟩

/-- Once loaded, quiet edges change nothing. -/
theorem loaded_run {ws : List (BitVec 64)} {bank : Bool} {old : Store.Image} (h : List Inputs)
    (s : State) (hl : Loaded ws bank old s) (hd : Delivers h []) :
    Loaded ws bank old (runWith A s h) := by
  induction h generalizing s with
  | nil => exact hl
  | cons i rest ih =>
    cases hd with
    | quiet hq hd' => exact ih _ (loaded_quiet A hl i hq) hd'

/-- The next word, accepted: one more register of the staging bank is the image's. -/
theorem staging_push {ws : List (BitVec 64)} {k : Nat} {bank : Bool} {old : Store.Image} {s : State}
    (h : Staging ws k bank old s) (hk : k < 322)
    (hgood : goodWord (BitVec.ofNat 9 k) (ws.getD k 0) = true)
    (hA : A (BitVec.ofNat 9 k) (ws.getD k 0) = true) (i : Inputs)
    (hc : Carries i 2 (ws.getD k 0)) : Staging ws (k + 1) bank old (stepWith A i s) := by
  have hcursor : s.control.cursor = BitVec.ofNat 9 k := by
    apply BitVec.eq_of_toNat_eq
    rw [h.cursor, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hdata := (carries_plain hc (by decide)).2.2.2
  unfold stepWith
  rw [admitted_of_accept A i s (by rw [hcursor, hdata]; exact hA)]
  obtain ⟨hcontrol, hactive, hstaging, hidle⟩ := pushed_next i s _ hc h.idle h.pending
    (by rw [h.cursor]; exact hk) (by rw [hcursor]; exact hgood)
  rw [h.active] at hactive hstaging
  refine ⟨by rw [hcontrol]; exact h.active, by rw [hcontrol]; exact h.pending, ?_, hidle, ?_,
    fun r => by rw [hactive]; exact h.kept r⟩
  · rw [hcontrol]
    show (s.control.cursor - 511).toNat = k + 1
    rw [Loader.cursor_increment _ (by rw [h.cursor]; exact hk), h.cursor]
  · intro w r hr
    rw [hstaging]
    by_cases he : s.control.cursor = Store.offset r
    · have hoff : (Store.offset r).toNat = k := by rw [← he, h.cursor]
      simp [Store.tick, he, imageOf, hoff]
    · have hne : (Store.offset r).toNat ≠ k := by
        intro hoff
        apply he
        apply BitVec.eq_of_toNat_eq
        rw [h.cursor, hoff]
      simp only [Store.tick, Bool.true_and, beq_iff_eq, he, if_false]
      exact h.staged r (by omega)

/-- The commit of a complete upload. -/
theorem staging_commit {ws : List (BitVec 64)} {bank : Bool} {old : Store.Image} {s : State}
    (h : Staging ws 322 bank old s) (i : Inputs) (d : BitVec 64) (hc : Carries i 3 d) :
    Loaded ws bank old (stepWith A i s) := by
  have hcmd := (carries_plain hc (by decide)).2.2.1
  unfold stepWith
  rw [admitted_of_command A i s (by rw [hcmd]; rfl)]
  have hcommit := complete_commits i s d hc h.idle h.pending h.cursor
  refine ⟨?_, fun r => ?_, fun r => ?_, ?_⟩
  · rw [(commit_switches_image i s hcommit (Store.Register.idle)).1, h.active]
  · rw [commit_does_not_write i s hcommit]
    exact h.staged r (offset_lt r)
  · rw [commit_does_not_write i s hcommit]
    exact h.kept r
  · rw [commit_resets_execution i s hcommit, h.active, h.staged .idle (offset_lt .idle)]

/-- From any point of the upload to its end. -/
theorem staged_run (ws : List (BitVec 64)) (hlen : ws.length = 322)
    (hgood : ∀ k, k < 322 → goodWord (BitVec.ofNat 9 k) (ws.getD k 0) = true)
    (hA : ∀ k, k < 322 → A (BitVec.ofNat 9 k) (ws.getD k 0) = true) (d : BitVec 64)
    (h : List Inputs) (s : State) (done rest : List (BitVec 64)) (hws : ws = done ++ rest)
    {bank : Bool} {old : Store.Image} (hs : Staging ws done.length bank old s)
    (hd : Delivers h (rest.map (fun w => ((2 : BitVec 3), w)) ++ [(3, d)])) :
    Loaded ws bank old (runWith A s h) := by
  induction h generalizing s done rest with
  | nil =>
    cases rest with
    | nil => simp only [List.map_nil, List.nil_append] at hd; cases hd
    | cons w' rest' => simp only [List.map_cons, List.cons_append] at hd; cases hd
  | cons m h' ih =>
    cases rest with
    | nil =>
      simp only [List.map_nil, List.nil_append] at hd
      cases hd with
      | quiet hq hd' =>
        exact ih (stepWith A m s) done [] hws (staging_quiet A hs m hq)
          (by simpa only [List.map_nil, List.nil_append] using hd')
      | command hc hd' =>
        have hfull : done.length = 322 := by rw [← hlen, hws, List.append_nil]
        exact loaded_run A h' _ (staging_commit A (hfull ▸ hs) m d hc) hd'
    | cons w' rest' =>
      simp only [List.map_cons, List.cons_append] at hd
      cases hd with
      | quiet hq hd' =>
        exact ih (stepWith A m s) done (w' :: rest') hws (staging_quiet A hs m hq)
          (by simpa only [List.map_cons, List.cons_append] using hd')
      | command hc hd' =>
        have hk : done.length < 322 := by
          have := congrArg List.length hws
          simp only [List.length_append, List.length_cons] at this
          omega
        have hword : ws.getD done.length 0 = w' := by
          rw [hws]
          simp
        have hstep := staging_push A hs hk (hgood _ hk) (hA _ hk) m (by rw [hword]; exact hc)
        exact ih (stepWith A m s) (done ++ [w']) rest' (by rw [hws]; simp)
          (by simpa only [List.length_append, List.length_cons, List.length_nil] using hstep) hd'

/-- **The upload theorem.** With the engine stopped, any history that delivers
begin, the 322 words and commit — however spaced — leaves the other bank
selected and valid, holding exactly those words; the bank that was active
untouched; and the engine stopped with the new image's idle pins. -/
theorem upload_loads (ws : List (BitVec 64)) (hlen : ws.length = 322)
    (hgood : ∀ k, k < 322 → goodWord (BitVec.ofNat 9 k) (ws.getD k 0) = true)
    (hA : ∀ k, k < 322 → A (BitVec.ofNat 9 k) (ws.getD k 0) = true) (d₀ d₁ : BitVec 64)
    (h : List Inputs) (s : State) (hidle : Reactive.runningValue s.core = false)
    (hd : Delivers h (uploadCommands ws d₀ d₁)) :
    Loaded ws s.control.active (s.memory s.control.active) (runWith A s h) := by
  unfold uploadCommands at hd
  suffices ∀ (bank : Bool) (old : Store.Image) (s : State), Reactive.runningValue s.core = false →
      s.control.active = bank → (∀ {w : Nat} (r : Store.Register w), s.memory bank r = old r) →
      Loaded ws bank old (runWith A s h) from
    this s.control.active (s.memory s.control.active) s hidle rfl (fun _ => rfl)
  intro bank old
  induction h with
  | nil => cases hd
  | cons m h' ih =>
    intro s hidle hactive hkept
    cases hd with
    | quiet hq hd' =>
      have hstep : stepWith A m s = next m s := by
        unfold stepWith
        rw [admitted_of_command A m s (quiet_command hq)]
      obtain ⟨hcontrol, hmemory, hidle', _⟩ := quiet_next m s hq hidle
      exact ih hd' (stepWith A m s) (by rw [hstep]; exact hidle')
        (by rw [hstep, hcontrol]; exact hactive) (fun r => by rw [hstep, hmemory]; exact hkept r)
    | command hc hd' =>
      have hcmd := (carries_plain hc (by decide)).2.2.1
      have hstep : stepWith A m s = next m s := by
        unfold stepWith
        rw [admitted_of_command A m s (by rw [hcmd]; rfl)]
      obtain ⟨hcontrol, hmemory, hidle'⟩ := begin_next m s d₀ hc hidle
      have hs : Staging ws ([] : List (BitVec 64)).length bank old (stepWith A m s) := by
        rw [hstep]
        exact ⟨by rw [hcontrol]; exact hactive, by rw [hcontrol], by rw [hcontrol]; rfl, hidle',
          fun r hr => absurd hr (Nat.not_lt_zero _), fun r => by rw [hmemory]; exact hkept r⟩
      exact staged_run A ws hlen hgood hA d₁ h' _ [] ws rfl hs hd'

/-- The machine itself admits every word. -/
theorem runWith_all (s : State) (h : List Inputs) : runWith (fun _ _ => true) s h = run s h := by
  induction h generalizing s with
  | nil => rfl
  | cons i rest ih =>
    show runWith _ (next (admitted _ i s) s) rest = run (next i s) rest
    rw [admitted_all, ih]

end Pinwheel.Hardware.Loader.Machine
