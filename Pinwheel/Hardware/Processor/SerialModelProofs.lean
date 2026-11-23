import Pinwheel.Hardware.Processor.SerialModel

namespace Pinwheel.Hardware.Processor.SerialModel

theorem cpu_input_eq (d : Uart.Timing) (i : Input) (s : State) :
    MmioModel.cpuState (mmioInput d i s) s.mmio = cpuState i s := rfl

theorem cpu_busy (i : Input) (s : State) (byte : Uart.Byte) (h : s.mmio.tx = some byte) :
    (cpuState i s).tx = some byte := by
  cases ho : i.operation with
  | none => simpa [cpuState, cpuInput, MmioModel.cpuState, ho] using h
  | some r => simpa [cpuState, cpuInput, MmioModel.cpuState, ho] using
      MmioModel.access_busy_tx i.gpioInput r s.mmio byte h

theorem cpu_idle (i : Input) (s : State) (hr : i.reset = false) (ht : s.mmio.tx = none) :
    (cpuState i s).tx = txWrite i s := by
  cases ho : i.operation with
  | none => simp [cpuState, cpuInput, MmioModel.cpuState, txWrite, hr, ho, ht]
  | some r =>
    simp only [cpuState, cpuInput, MmioModel.cpuState, txWrite, hr, ho]
    unfold MmioModel.access
    repeat' split
    all_goals simp_all

theorem tx_acceptance (i : Input) (s : State) (owned : Owned s) :
    Uart.accepted (uartInput i s) s.uart.tx = txWrite i s := by
  cases hr : i.reset
  · cases ht : s.uart.tx with
    | idle =>
      have hm : s.mmio.tx = none := by simpa [Owned, ht, Uart.txPending] using owned
      simpa [Uart.accepted, Uart.txReady, uartInput, hr, ht] using cpu_idle i s hr hm
    | active byte elapsed =>
      have hm : s.mmio.tx = some byte := by simpa [Owned, ht, Uart.txPending] using owned
      cases ho : i.operation <;> simp [Uart.accepted, Uart.txReady, uartInput, hr, txWrite, ho, hm]
  · simp [Uart.accepted, Uart.txReady, uartInput, hr, txWrite]

theorem step_owned (d : Uart.Timing) (i : Input) (s : State) (owned : Owned s) :
    Owned (step d i s) := by
  cases hr : i.reset
  · cases ht : s.uart.tx with
    | idle =>
      have hm : s.mmio.tx = none := by simpa [Owned, ht, Uart.txPending] using owned
      simp only [Owned, step, MmioModel.step, mmioInput, Uart.observe, uartInput, hr,
        Bool.false_eq_true, ↓reduceIte, MmioModel.autonomous, MmioModel.receive_tx,
        MmioModel.completedTx, Uart.completed, ht, Uart.step, Uart.txStep, Uart.txPending]
      change (cpuState i s).tx = Uart.txPending (match (cpuState i s).tx with
        | none => .idle | some byte => .active byte 0)
      cases (cpuState i s).tx <;> rfl
    | active byte elapsed =>
      have hm : s.mmio.tx = some byte := by simpa [Owned, ht, Uart.txPending] using owned
      have hc := cpu_busy i s byte hm
      by_cases done : d.frame ≤ elapsed+1
      all_goals simp [Owned, step, MmioModel.step, MmioModel.autonomous, MmioModel.completedTx,
        mmioInput, Uart.observe, uartInput, hr, ht, hm, Uart.completed, Uart.step, Uart.txStep,
        Uart.txPending, done, hc]
      change (cpuState i s).tx = some byte
      exact hc
  · simp [Owned, step, MmioModel.step, mmioInput, uartInput, hr, MmioModel.initial,
      Uart.step, Uart.txStep, Uart.txPending]

theorem initial_valid (d : Uart.Timing) : Valid d initial :=
  ⟨rfl, Uart.initial_valid d⟩

theorem step_valid (d : Uart.Timing) (i : Input) (s : State) (owned : Owned s) :
    Valid d (step d i s) := ⟨step_owned d i s owned, Uart.step_valid _ _ _⟩

theorem reset_step (d : Uart.Timing) (i : Input) (s : State) (hr : i.reset = true) :
    step d i s = initial := by
  simp [step, mmioInput, uartInput, hr, MmioModel.step, Uart.step, Uart.txStep, Uart.rxStep,
    initial, Uart.initial]

theorem reset_output (d : Uart.Timing) (i : Input) (s : State) (hr : i.reset = true) :
    observe d i s = ⟨none, 0, ⟨true, false, false, none, false⟩⟩ := by
  simp [observe, mmioInput, uartInput, hr, MmioModel.observe, Uart.observe,
    Uart.txLine, Uart.txReady, Uart.completed, Uart.arrival, Uart.framingError]

theorem run_valid (d : Uart.Timing) (s : State) (hs : Valid d s) (traffic : List Input) :
    Valid d ((component d).run s traffic) := by
  induction traffic generalizing s with
  | nil => exact hs
  | cons i rest ih => exact ih _ (step_valid d i s hs.1)

theorem completion_owned (d : Uart.Timing) (i : Input) (s : State) (owned : Owned s) :
    MmioModel.completedTx (mmioInput d i s) s.mmio = txComplete d i s := by
  cases hr : i.reset <;> cases ht : s.uart.tx with
  | idle => simp [MmioModel.completedTx, mmioInput, Uart.observe, Uart.completed, uartInput, hr,
      ht, txComplete]
  | active byte elapsed =>
    have hm : s.mmio.tx = some byte := by simpa [Owned, ht, Uart.txPending] using owned
    by_cases done : d.frame ≤ elapsed+1 <;>
      simp [MmioModel.completedTx, mmioInput, Uart.observe, Uart.completed, uartInput, hr,
        ht, txComplete, done, hm]

theorem tx_edge_balance (d : Uart.Timing) (i : Input) (s : State) (owned : Owned s) :
    s.mmio.tx.toList ++ (txWrite i s).toList =
      txRetired d i s ++ (step d i s).mmio.tx.toList := by
  have equation := Uart.tx_balance d (uartInput i s) s.uart.tx
  rw [tx_acceptance i s owned, ← owned] at equation
  have hc : Uart.canceled (uartInput i s) s.uart.tx = txCancel i s := by
    change s.mmio.tx = Uart.txPending s.uart.tx at owned
    simp only [Uart.canceled, uartInput, txCancel, ← owned]
  have hn : Uart.txPending (Uart.txStep d (uartInput i s) s.uart.tx) = (step d i s).mmio.tx :=
    (step_owned d i s owned).symm
  simpa only [txRetired, txComplete, hc, hn, List.append_assoc] using equation

theorem tx_history_balance (d : Uart.Timing) (s : State) (owned : Owned s) (traffic : List Input) :
    s.mmio.tx.toList ++ history d (fun i s => (txWrite i s).toList) s traffic =
      history d (txRetired d) s traffic ++ ((component d).run s traffic).mmio.tx.toList := by
  induction traffic generalizing s with
  | nil => simp [history, Timed.Component.run]
  | cons i rest ih =>
    simp only [history, Timed.Component.run, component]
    rw [← List.append_assoc, tx_edge_balance d i s owned]
    simpa only [List.append_assoc, component] using congrArg (txRetired d i s ++ ·)
      (ih (step d i s) (step_owned d i s owned))

theorem successful_write_starts (d : Uart.Timing) (i : Input) (s : State) (data : BitVec 32)
    (owned : Owned s) (hr : i.reset = false)
    (ho : i.operation = some ⟨.uart, 1, true, data⟩) (ht : s.mmio.tx = none) :
    (observe d i s).response = some .stored ∧
    (step d i s).uart.tx = .active (data.extractLsb' 0 8) 0 ∧
    (observe d i (step d i s)).frontend.line = false := by
  have acceptance : Uart.accepted (uartInput i s) s.uart.tx = some (data.extractLsb' 0 8) := by
    rw [tx_acceptance i s owned]
    simp [txWrite, hr, ho, ht]
  have started := Uart.accept_start d (uartInput i s) s.uart.tx _ acceptance
  refine ⟨(MmioModel.tx_start (mmioInput d i s) s.mmio data hr ho ht).1, started.1, ?_⟩
  change Uart.txLine d (uartInput i (step d i s)) (step d i s).uart.tx = false
  have hx : (step d i s).uart.tx = .active (data.extractLsb' 0 8) 0 := started.1
  simp [hx, Uart.txLine, uartInput, hr, Uart.frameBit]

theorem completion_clears (d : Uart.Timing) (i : Input) (s : State) (byte : Uart.Byte)
    (owned : Owned s) (hc : txComplete d i s = some byte) :
    (step d i s).uart.tx = .idle ∧ (step d i s).mmio.tx = none := by
  have hu : (step d i s).uart.tx = .idle := Uart.completion_idle d _ _ byte hc
  exact ⟨hu, (step_owned d i s owned).trans (by simp [hu, Uart.txPending])⟩

/-- No held-byte retransmission is possible on the next edge. Only a fresh
successful TXDATA write can create another acceptance, even for an equal byte. -/
theorem no_reaccept_without_write (d : Uart.Timing) (i next : Input) (s : State)
    (owned : Owned s) (hn : next.operation = none) :
    Uart.accepted (uartInput next (step d i s)) (step d i s).uart.tx = none := by
  rw [tx_acceptance next _ (step_owned d i s owned)]
  simp [txWrite, hn]

theorem busy_write_completion (d : Uart.Timing) (i : Input) (s : State) (data : BitVec 32)
    (byte : Uart.Byte) (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 1, true, data⟩)
    (ht : s.mmio.tx = some byte) (hc : txComplete d i s = some byte) :
    (observe d i s).response = some (.fault .txBusy) ∧ (step d i s).mmio.tx = none := by
  apply MmioModel.tx_busy_complete (mmioInput d i s) s.mmio data byte hr ho ht
  change (txComplete d i s).isSome = true
  simp [hc]

theorem rx_step_independent (d : Uart.Timing) (i : Input) (s : State) :
    (step d i s).uart.rx = Uart.rxStep d ⟨i.reset, none, i.rx⟩ s.uart.rx := rfl

theorem rx_arrival_independent (d : Uart.Timing) (i : Input) (s : State) :
    (mmioInput d i s).rxArrival = Uart.arrival d ⟨i.reset, none, i.rx⟩ s.uart.rx := rfl

theorem cpu_rx_frame (i : Input) (s : State) :
    (cpuState i s).rx = s.mmio.rx ∨ (cpuState i s).rx = none := by
  cases ho : i.operation with
  | none => exact Or.inl (by simp [cpuState, cpuInput, MmioModel.cpuState, ho])
  | some r =>
    simp only [cpuState, cpuInput, MmioModel.cpuState, ho]
    unfold MmioModel.access
    repeat' split
    all_goals simp_all

theorem rx_disposition (d : Uart.Timing) (i : Input) (s : State) :
    (rxAccepted d i s).toList ++ (rxDropped d i s).toList = (mmioInput d i s).rxArrival.toList := by
  cases hx : (cpuState i s).rx <;> simp [rxAccepted, rxDropped, hx]

theorem rx_edge_balance (d : Uart.Timing) (i : Input) (s : State) :
    s.mmio.rx.toList ++ (rxAccepted d i s).toList =
      rxRetired i s ++ (step d i s).mmio.rx.toList := by
  cases hr : i.reset
  · have frame := cpu_rx_frame i s
    cases old : s.mmio.rx <;> cases current : (cpuState i s).rx <;>
      cases arrival : (mmioInput d i s).rxArrival
    all_goals simp_all only [Option.some_ne_none, reduceCtorEq, false_or, or_false, Option.some.injEq]
    all_goals simp only [rxAccepted, rxRetired, rxConsumed, rxCancel, hr,
      Bool.false_eq_true, ↓reduceIte, step, MmioModel.step, show (mmioInput d i s).reset = false from hr,
      MmioModel.autonomous, cpu_input_eq, MmioModel.receive, arrival, current, old]
    all_goals simp_all
  · simp [rxAccepted, rxRetired, rxConsumed, rxCancel, hr, reset_step d i s hr,
      mmioInput, Uart.observe, Uart.arrival, uartInput, initial, MmioModel.initial]

theorem rx_history_balance (d : Uart.Timing) (s : State) (traffic : List Input) :
    s.mmio.rx.toList ++ history d (fun i s => (rxAccepted d i s).toList) s traffic =
      history d rxRetired s traffic ++ ((component d).run s traffic).mmio.rx.toList := by
  induction traffic generalizing s with
  | nil => simp [history, Timed.Component.run]
  | cons i rest ih =>
    simp only [history, Timed.Component.run, component]
    rw [← List.append_assoc, rx_edge_balance d i s]
    simpa only [List.append_assoc, component] using congrArg (rxRetired i s ++ ·) (ih (step d i s))

theorem consume_arrival (d : Uart.Timing) (i : Input) (s : State) (data : BitVec 32)
    (old new : Uart.Byte) (hr : i.reset = false)
    (ho : i.operation = some ⟨.uart, 2, false, data⟩) (hx : s.mmio.rx = some old)
    (ha : Uart.arrival d ⟨i.reset, none, i.rx⟩ s.uart.rx = some new) :
    (observe d i s).response = some (.read (old.setWidth 32)) ∧
    (step d i s).mmio.rx = some new ∧ (step d i s).mmio.overrun = s.mmio.overrun :=
  MmioModel.rx_consume_arrival (mmioInput d i s) s.mmio data old new hr ho hx ha

theorem empty_read_arrival (d : Uart.Timing) (i : Input) (s : State) (data : BitVec 32)
    (new : Uart.Byte) (hr : i.reset = false)
    (ho : i.operation = some ⟨.uart, 2, false, data⟩) (hx : s.mmio.rx = none)
    (ha : Uart.arrival d ⟨i.reset, none, i.rx⟩ s.uart.rx = some new) :
    (observe d i s).response = some (.fault .rxEmpty) ∧
    (step d i s).mmio.rx = some new ∧ (step d i s).mmio.overrun = s.mmio.overrun :=
  MmioModel.rx_empty_arrival (mmioInput d i s) s.mmio data new hr ho hx ha

theorem framing_over_clear (d : Uart.Timing) (i : Input) (s : State) (data : BitVec 32)
    (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 3, true, data⟩)
    (hf : Uart.framingError d ⟨i.reset, none, i.rx⟩ s.uart.rx = true) :
    (observe d i s).response = some .stored ∧ (step d i s).mmio.framing = true := by
  simp [observe, step, MmioModel.observe, MmioModel.step, MmioModel.cpuState, MmioModel.access,
    MmioModel.autonomous, mmioInput, Uart.observe, hr, ho]
  exact Or.inr hf

theorem overrun_over_clear (d : Uart.Timing) (i : Input) (s : State) (data : BitVec 32)
    (old new : Uart.Byte) (hr : i.reset = false)
    (ho : i.operation = some ⟨.uart, 3, true, data⟩) (hx : s.mmio.rx = some old)
    (ha : Uart.arrival d ⟨i.reset, none, i.rx⟩ s.uart.rx = some new) :
    (observe d i s).response = some .stored ∧
    (step d i s).mmio.rx = some old ∧ (step d i s).mmio.overrun = true := by
  have arrival : (mmioInput d i s).rxArrival = some new := ha
  simp [observe, MmioModel.observe, step, MmioModel.step, show (mmioInput d i s).reset = false from hr,
    show (mmioInput d i s).operation = some ⟨.uart, 3, true, data⟩ from ho, MmioModel.autonomous,
    MmioModel.cpuState, MmioModel.access, MmioModel.receive, arrival, hx]

theorem access_consumed_response (gpio : BitVec 32) (r : MmioModel.Request) (s : MmioModel.State)
    (byte : Uart.Byte) (before : s.rx = some byte) (after : (MmioModel.access gpio r s).2.rx = none) :
    (MmioModel.access gpio r s).1 = .read (byte.setWidth 32) := by
  unfold MmioModel.access at *
  repeat' split at *
  all_goals simp_all

theorem consumed_response (d : Uart.Timing) (i : Input) (s : State) (byte : Uart.Byte)
    (hc : rxConsumed i s = some byte) : (observe d i s).response = some (.read (byte.setWidth 32)) := by
  cases hr : i.reset
  · have info : (cpuState i s).rx = none ∧ s.mmio.rx = some byte := by
      simpa [rxConsumed, hr] using hc
    cases ho : i.operation with
    | none =>
      have absent : s.mmio.rx = none := by simpa [cpuState, cpuInput, MmioModel.cpuState, ho] using info.1
      simp [absent] at info
    | some r =>
      have after : (MmioModel.access i.gpioInput r s.mmio).2.rx = none := by
        simpa [cpuState, cpuInput, MmioModel.cpuState, ho] using info.1
      have answer := access_consumed_response i.gpioInput r s.mmio byte info.2 after
      simpa only [observe, MmioModel.observe, mmioInput, hr, ho, Bool.false_eq_true, ↓reduceIte,
        Option.map_some] using congrArg some answer
  · simp [rxConsumed, hr] at hc

/-- Every actual CPU, timer, completion, receive/drop, error and reset event
replays the complete device state; reset never erases earlier history. -/
theorem device_history_replay (d : Uart.Timing) (s : State) (traffic : List Input) :
    MmioModel.replay s.mmio (history d (deviceEvents d) s traffic) =
      some ((component d).run s traffic).mmio := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [history, deviceEvents, MmioModel.replay_append, MmioModel.replay_events, Option.bind_some,
      Timed.Component.run, component]
    exact ih (step d i s)

end Pinwheel.Hardware.Processor.SerialModel
