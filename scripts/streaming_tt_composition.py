"""Concrete arbitrary-state OriginalDevice to typed-package composition.

This emits proof obligations only. Acceptance requires native checking against
the complete generated state, wiring, component and endpoint modules.
"""
from streaming_tt_graph import header


def generate():
    imports = ['PhysicalGRTComponentWires', 'PhysicalGRTPhysicalInputs',
        'PhysicalFrontendStateJoin', 'PhysicalCoreStateJoin',
        'PhysicalFrontendNextJoin', 'PhysicalCoreNextJoin', 'PhysicalGRTPublicOutputs',
        'OptimizedFrontendProof', 'OptimizedCoreD2Proof',
        'Pinwheel.Hardware.StreamingPhysical.State']
    text = header(imports, 'Pinwheel.Artifact.StreamingPhysicalGRT.Join') + r'''
open Pinwheel.Hardware

def decodedState (bits : Fin 6039 → Bool) : StreamingReady.Package.State 1 :=
  packageState (%PACK%.decode bits)

abbrev physicalValues (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) : Nat → Bool :=
  Original.network.value (Device.environment input bits)

theorem decoded_state_ext (left right : StreamingReady.Package.State 1)
    (frontendEq : left.frontend = right.frontend)
    (coreEq : left.core = right.core) : left = right := by
  cases left
  cases right
  cases frontendEq
  cases coreEq
  rfl

theorem frontend_step_typed (i : Values Streaming.Frontend.Input)
    (s : Values Streaming.Frontend.Register) (field : Streaming.Frontend.Register w) :
    %FE%.step i s field = Streaming.Frontend.circuit.step i s field :=
  (%FE%.step_correct i s field).trans
    (Pinwheel.Artifact.StreamingOptimizedFrontend.step_correct i s field)

theorem frontend_observe_typed (i : Values Streaming.Frontend.Input)
    (s : Values Streaming.Frontend.Register) (field : Streaming.Frontend.Output w) :
    %FE%.observe i s field = Streaming.Frontend.circuit.observe i s field :=
  (%FE%.observe_correct i s field).trans
    (Pinwheel.Artifact.StreamingOptimizedFrontend.observe_correct i s field)

theorem core_step_typed (i : Values Streaming.Core.Input)
    (s : Values (Streaming.Core.Register 1)) (field : Streaming.Core.Register 1 w) :
    %CORE%.step i s field = (StreamingReady.Core.circuit 1).step i s field :=
  (%CORE%.step_correct i s field).trans
    (Pinwheel.Artifact.StreamingOptimizedCoreD2.step_correct i s field)

theorem core_observe_typed (i : Values Streaming.Core.Input)
    (s : Values (Streaming.Core.Register 1)) (field : Streaming.Core.Output w) :
    %CORE%.observe i s field = (StreamingReady.Core.circuit 1).observe i s field :=
  (%CORE%.observe_correct i s field).trans
    (Pinwheel.Artifact.StreamingOptimizedCoreD2.observe_correct i s field)

theorem frontend_state_typed (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    (FrontendEmbedding.readState (physicalValues input bits) : Values Streaming.Frontend.Register) = (fun {w} field => (decodedState bits).frontend field) :=
  FrontendEmbedding.readState_correct input bits

theorem core_state_typed (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    (CoreEmbedding.readState (physicalValues input bits) : Values (Streaming.Core.Register 1)) = (fun {w} field => (decodedState bits).core field) :=
  CoreEmbedding.readState_correct input bits

theorem core_inputs_typed (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    (CoreEmbedding.readInputs (physicalValues input bits) : Values Streaming.Core.Input) =
      (fun {w} port => (decodedState bits).coreInputs (StreamingReady.Package.Components.typed 1) (enginePins input) port) := by
  rw [core_wires (Device.environment input bits)]
  rw [physical_wires input bits, frontend_state_typed input bits]
  funext width port
  exact (frontend_observe_typed _ _ (.core port)).trans
    (Streaming.Package.coreInput_independent (enginePins input) (decodedState bits).frontend
      (fun {w} field => FrontendEmbedding.readInputs (physicalValues input bits) (.status field))
      (fun {w} _ => 0) port)

theorem status_typed (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    (fun {w} port => FrontendEmbedding.readInputs (physicalValues input bits) (.status port) :
      Values Streaming.Core.Output) =
      (fun {w} port => (decodedState bits).status (StreamingReady.Package.Components.typed 1) (enginePins input) port) := by
  rw [status_wires (Device.environment input bits)]
  rw [core_inputs_typed input bits, core_state_typed input bits]
  funext width port
  exact core_observe_typed _ _ port

theorem frontend_inputs_typed (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    (FrontendEmbedding.readInputs (physicalValues input bits) : Values Streaming.Frontend.Input) =
      (fun {w} port => (decodedState bits).frontendInputs (StreamingReady.Package.Components.typed 1) (enginePins input) port) := by
  rw [physical_wires input bits, status_typed input bits]
  rfl

theorem decoded_frontend_next (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    ((decodedState (OriginalState.device.step input bits)).frontend : Values Streaming.Frontend.Register) =
      (fun {w} field => ((decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input)).frontend field) := by
  rw [show ((decodedState (OriginalState.device.step input bits)).frontend : Values Streaming.Frontend.Register) =
    (fun {w} field => %FE%.step (FrontendEmbedding.readInputs (physicalValues input bits))
      (FrontendEmbedding.readState (physicalValues input bits)) field) from
        FrontendEmbedding.next_component input bits]
  rw [frontend_inputs_typed input bits, frontend_state_typed input bits]
  funext width field
  exact frontend_step_typed _ _ field

theorem decoded_core_next (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    ((decodedState (OriginalState.device.step input bits)).core : Values (Streaming.Core.Register 1)) =
      (fun {w} field => ((decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input)).core field) := by
  rw [show ((decodedState (OriginalState.device.step input bits)).core : Values (Streaming.Core.Register 1)) =
    (fun {w} field => %CORE%.step (CoreEmbedding.readInputs (physicalValues input bits))
      (CoreEmbedding.readState (physicalValues input bits)) field) from
        CoreEmbedding.next_component input bits]
  rw [core_inputs_typed input bits, core_state_typed input bits]
  funext width field
  exact core_step_typed _ _ field

theorem decoded_step (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    decodedState (OriginalState.device.step input bits) =
      (decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input) := by
  exact decoded_state_ext _ _ (decoded_frontend_next input bits) (decoded_core_next input bits)

theorem logical_outputs_typed (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    (logicalOutputs input bits : Values StreamingReady.Package.Output) =
      (fun {w} port => (decodedState bits).observe (StreamingReady.Package.Components.typed 1) (enginePins input) port) := by
  funext width port
  cases port with
  | miso =>
    change %FE%.observe _ _ .miso = _
    rw [frontend_inputs_typed input bits, frontend_state_typed input bits]
    exact frontend_observe_typed _ _ .miso
  | ready =>
    change %FE%.observe _ _ .ready = _
    rw [frontend_inputs_typed input bits, frontend_state_typed input bits]
    exact frontend_observe_typed _ _ .ready
  | busy =>
    change %CORE%.observe _ _ .busy = _
    rw [core_inputs_typed input bits, core_state_typed input bits]
    exact core_observe_typed _ _ .busy
  | levels =>
    change %CORE%.observe _ _ .levels = _
    rw [core_inputs_typed input bits, core_state_typed input bits]
    exact core_observe_typed _ _ .levels
  | enabled =>
    change %CORE%.observe _ _ .enabled = _
    rw [core_inputs_typed input bits, core_state_typed input bits]
    exact core_observe_typed _ _ .enabled

theorem decoded_observe (input : Fin 18 → Bool) (bits : Fin 6039 → Bool)
    (pad : StreamingReady.TinyWiring.Pad) :
    originalPads input bits pad =
      StreamingReady.TinyWiring.Description.pads (StreamingReady.TinyWiring.canonical 1) (pins input)
        ((decodedState bits).observe (StreamingReady.Package.Components.typed 1) (enginePins input)) pad := by
  cases pad with
  | uo =>
    rw [original_pad_uo_out, logical_outputs_typed, %TINY%.uo_out_correct]
    rfl
  | uio =>
    rw [original_pad_uio_out, logical_outputs_typed, %TINY%.uio_out_correct]
    rfl
  | oe =>
    rw [original_pad_uio_oe, logical_outputs_typed, %TINY%.uio_oe_correct]
    rfl

theorem decoded_run (bits : Fin 6039 → Bool) (incoming : List (Fin 18 → Bool)) :
    decodedState (OriginalState.device.run bits incoming) =
      (decodedState bits).run (StreamingReady.Package.Components.typed 1) (incoming.map enginePins) := by
  induction incoming generalizing bits with
  | nil => rfl
  | cons input rest induction =>
    change decodedState (OriginalState.device.run (OriginalState.device.step input bits) rest) = _
    rw [induction, decoded_step input bits]
    rfl

theorem decoded_encode (state : StreamingReady.Package.State 1) :
    decodedState (%PACK%.encode (stateValues state)) = state := by
  rw [decodedState, %PACK%.decode_encode, packageState_stateValues]

theorem encoded_decoded (bits : Fin 6039 → Bool) :
    %PACK%.encode (stateValues (decodedState bits)) = bits := by
  rw [decodedState, stateValues_packageState, %PACK%.encode_decode]

end Pinwheel.Artifact.StreamingPhysicalGRT.Join
'''
    for token, value in {
        '%PACK%': 'Pinwheel.Artifact.StreamingPhysicalState.packing',
        '%FE%': 'Pinwheel.Artifact.StreamingPhysicalFrontend.Component',
        '%CORE%': 'Pinwheel.Artifact.StreamingPhysicalCore.Component',
        '%TINY%': 'Pinwheel.Artifact.StreamingOptimizedTinyD2',
    }.items():
        text = text.replace(token, value)
    return {'PhysicalGRTTypedJoin': text}


def generate_actual(*, actual_module='PhysicalGRTActualProof',
                    actual_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.ActualProof',
                    actual_device='Pinwheel.Artifact.StreamingPhysicalGRT.ActualState.device',
                    clock_module='ActualGRTClockDAGProof',
                    clock_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.ActualClockDAG'):
    """Join the actual full-state transport and complete CTS graph to typed behavior."""
    text = header(['PhysicalGRTTypedJoin', 'PhysicalGRTOriginalProof', actual_module,
        clock_module, 'ActualGRTClockInventory'], 'Pinwheel.Artifact.StreamingPhysicalGRT.Final') + r'''
open Pinwheel.Hardware
open Pinwheel.Artifact.StreamingPhysicalGRT.Join

theorem actual_step_original (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    %DEVICE%.step input bits = OriginalState.device.step input bits := by
  funext index
  exact (%ACTUAL%.step_correct input bits index).trans
    (OriginalProof.step_correct input bits index).symm

theorem decoded_actual_step (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    decodedState (%DEVICE%.step input bits) =
      (decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input) := by
  rw [actual_step_original, decoded_step]

theorem actual_step_encoded (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    %DEVICE%.step input bits =
      Pinwheel.Artifact.StreamingPhysicalState.packing.encode (stateValues
        ((decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input))) := by
  have encoded := congrArg (fun state : StreamingReady.Package.State 1 =>
    Pinwheel.Artifact.StreamingPhysicalState.packing.encode (stateValues state))
      (decoded_actual_step input bits)
  rw [encoded_decoded] at encoded
  exact encoded

def actualPads (input : Fin 18 → Bool) (bits : Fin 6039 → Bool)
    (pad : StreamingReady.TinyWiring.Pad) : BitVec 8 :=
  match pad with
  | .oe => Word.pack (fun bit => %DEVICE%.observe input bits ⟨0+bit.val,by have h:=bit.isLt; omega⟩)
  | .uio => Word.pack (fun bit => %DEVICE%.observe input bits ⟨8+bit.val,by have h:=bit.isLt; omega⟩)
  | .uo => Word.pack (fun bit => %DEVICE%.observe input bits ⟨16+bit.val,by have h:=bit.isLt; omega⟩)

theorem actual_pads_original (input : Fin 18 → Bool) (bits : Fin 6039 → Bool)
    (pad : StreamingReady.TinyWiring.Pad) : actualPads input bits pad = originalPads input bits pad := by
  cases pad <;> apply Word.from_bits <;> intro index within
  all_goals rw [actualPads, originalPads, Word.pack_bit _ index within, Word.pack_bit _ index within]
  all_goals exact (%ACTUAL%.observe_correct input bits _).trans
    (OriginalProof.observe_correct input bits _).symm

theorem decoded_actual_observe (input : Fin 18 → Bool) (bits : Fin 6039 → Bool)
    (pad : StreamingReady.TinyWiring.Pad) :
    actualPads input bits pad =
      StreamingReady.TinyWiring.Description.pads (StreamingReady.TinyWiring.canonical 1) (pins input)
        ((decodedState bits).observe (StreamingReady.Package.Components.typed 1) (enginePins input)) pad :=
  (actual_pads_original input bits pad).trans (decoded_observe input bits pad)

theorem decoded_actual_run (bits : Fin 6039 → Bool) (incoming : List (Fin 18 → Bool)) :
    decodedState (%DEVICE%.run bits incoming) =
      (decodedState bits).run (StreamingReady.Package.Components.typed 1) (incoming.map enginePins) := by
  have actual_original : %DEVICE%.run bits incoming = OriginalState.device.run bits incoming :=
    (%ACTUAL%.run_correct bits incoming).trans (OriginalProof.run_correct bits incoming).symm
  rw [actual_original, decoded_run]

/-- Evaluate every physical FF from its own retained CTS and reset root. -/
def physicalUpdate (before after : Bool) (input : Fin 18 → Bool)
    (bits : Fin 6039 → Bool) (index : Fin 6039) : Bool :=
  if (%CLOCK%.resetRoot index).eval (%CLOCK%.network.value (fun _ => after)) = true then
    if Rising ((%CLOCK%.clockRoot index).eval (%CLOCK%.network.value (fun _ => before)))
        ((%CLOCK%.clockRoot index).eval (%CLOCK%.network.value (fun _ => after))) then
      %DEVICE%.step input bits index
    else bits index
  else false

theorem physical_update_eq (before after : Bool) (input : Fin 18 → Bool)
    (bits : Fin 6039 → Bool) :
    physicalUpdate before after input bits =
      if Rising before after then %DEVICE%.step input bits else bits := by
  funext index
  rw [physicalUpdate, %CLOCK%.actual_inactive, if_pos rfl,
    %CLOCK%.actual_positive, %CLOCK%.actual_positive]
  by_cases edge : Rising before after <;> simp only [edge, ite_true, ite_false]

theorem decoded_physical_update (before after : Bool) (input : Fin 18 → Bool)
    (bits : Fin 6039 → Bool) :
    decodedState (physicalUpdate before after input bits) =
      if Rising before after then
        (decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input)
      else decodedState bits := by
  rw [physical_update_eq]
  by_cases edge : Rising before after
  · rw [if_pos edge, if_pos edge]
    exact decoded_actual_step input bits
  · rw [if_neg edge, if_neg edge]

end Pinwheel.Artifact.StreamingPhysicalGRT.Final
'''
    for token,value in {'%ACTUAL%':actual_namespace,'%DEVICE%':actual_device,
                        '%CLOCK%':clock_namespace}.items():
        text=text.replace(token,value)
    return {'PhysicalGRTActualTypedJoin':text}


def generate_clock_inventory(clock,actual):
    """Certify the exact polarity of every actual CTS output, including loads."""
    from streaming_tt_graph import lookup_source,atom_source
    from streaming_tt_finite import finite_forall
    from streaming_tt_certificate import canonical_model
    from streaming_mapped_liberty import require
    names=clock['actual_cone_cells'];positions={name:1+index for index,name in enumerate(names)}
    cts=clock['actual_clock_cells'];require(cts and len(cts)==len(set(cts)) and set(cts)<=set(positions),
        'Missing or aliased actual CTS gate inventory')
    require(actual['labels']==(('input','clk',0),) and tuple(node['name'] for node in actual['nodes'])==names,
        'CTS inventory differs from its complete actual checked graph')
    dependent={0};derived_cts=[]
    for index,node in enumerate(actual['nodes'],1):
        if any(source in dependent for source in node['sources']):
            dependent.add(index);derived_cts.append(node['name'])
    require(len(cts)==len(derived_cts) and set(cts)==set(derived_cts),
        'Incomplete or aliased actual CTS dependency inventory')
    order=clock.get('ff_order',())
    require(type(order) is tuple and len(order)==len(set(order))==6039 and
        set(actual.get('outputs',{}))=={'clock','reset'} and
        len(actual['outputs']['clock'])==len(actual['outputs']['reset'])==6039 and
        tuple(actual['outputs']['clock'])==clock.get('clock_roots') and
        tuple(actual['outputs']['reset'])==clock.get('reset_roots'),
        'Incomplete or changed all6039 physical FF clock/reset roots')
    canonical=canonical_model(actual);require(not canonical['nodes'],'CTS graph is not a one-clock polarity network')
    require(all(root==('wire',0,False) for root in canonical['outputs']['clock']) and
        all(root==('constant',True) for root in canonical['outputs']['reset']),
        'Actual physical FF clock/reset polarity changed')
    images=[canonical['image'][positions[name]] for name in cts]
    require(all(atom[0]=='wire' and atom[1]==0 for atom in images),'Actual CTS output is not a raw-clock polarity')
    inverted=[atom[2] for atom in images]
    count=len(cts);ns=clock['namespace'];reference=ns+'.Reference';transport=ns+'.Transport'
    lines=[header([clock['module']],ns+'.Inventory'),
        lookup_source('ctsRootTable',[atom_source(('wire',positions[name],False)) for name in cts],
            result_type='Atom',default='.constant false'),
        lookup_source('ctsInvertedTable',[str(value).lower() for value in inverted],result_type='Bool',default='false'),
        f'def ctsRoot (index : Fin {count}) : Atom := ctsRootTable index.val',
        f'def ctsInverted (index : Fin {count}) : Bool := ctsInvertedTable index.val',
        finite_forall('ctsBound', count, lambda index:
            f'(ctsRoot {index}).Bounded ({ns}.network.inputs + {ns}.network.nodes)'),
        finite_forall('ctsImage', count, lambda index:
            f'(ctsRoot {index}).rename {transport}.image = .wire 0 (ctsInverted {index})'),
        f'theorem all_actual_cts_levels (index : Fin {count}) (raw : Bool) :',
        f'    (ctsRoot index).eval ({ns}.network.value (fun _ => raw)) = (if ctsInverted index then !raw else raw) := by',
        f'  rw [{transport}.contraction.atom _ _ (ctsBound index), {ns}.transport_image, ctsImage index]',
        f'  change (if ctsInverted index then !({reference}.network.value (fun _ => raw) 0) else {reference}.network.value (fun _ => raw) 0) = _',
        f'  rw [Network.value_input {reference}.network (fun _ => raw) 0 (by decide)]',
        'end '+ns+'.Inventory','']
    return {'ActualGRTClockInventory':'\n\n'.join(lines)}


def generate_required(*, cts_count):
    """Pin the public all-state contract independently of helper theorem bodies."""
    from streaming_mapped_liberty import require
    require(type(cts_count) is int and cts_count > 0, 'Missing complete CTS count')
    text = header(['PhysicalGRTActualTypedJoin'],
        'Pinwheel.Artifact.StreamingPhysicalGRT.Required') + r'''
open Pinwheel.Hardware
open Pinwheel.Artifact.StreamingPhysicalGRT.Join

example (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    decodedState (ActualState.device.step input bits) =
      (decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input) :=
  Final.decoded_actual_step input bits

example (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    ActualState.device.step input bits =
      Pinwheel.Artifact.StreamingPhysicalState.packing.encode (stateValues
        ((decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input))) :=
  Final.actual_step_encoded input bits

example (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) (pad : StreamingReady.TinyWiring.Pad) :
    Final.actualPads input bits pad =
      StreamingReady.TinyWiring.Description.pads (StreamingReady.TinyWiring.canonical 1) (pins input)
        ((decodedState bits).observe (StreamingReady.Package.Components.typed 1) (enginePins input)) pad :=
  Final.decoded_actual_observe input bits pad

example (bits : Fin 6039 → Bool) (incoming : List (Fin 18 → Bool)) :
    decodedState (ActualState.device.run bits incoming) =
      (decodedState bits).run (StreamingReady.Package.Components.typed 1) (incoming.map enginePins) :=
  Final.decoded_actual_run bits incoming

example (before after : Bool) (input : Fin 18 → Bool) (bits : Fin 6039 → Bool) :
    decodedState (Final.physicalUpdate before after input bits) =
      if Rising before after then
        (decodedState bits).step (StreamingReady.Package.Components.typed 1) (enginePins input)
      else decodedState bits := Final.decoded_physical_update before after input bits

example (bits : Fin 6039 → Bool) :
    Pinwheel.Artifact.StreamingPhysicalState.packing.encode (stateValues (decodedState bits)) = bits :=
  encoded_decoded bits

example (state : StreamingReady.Package.State 1) :
    decodedState (Pinwheel.Artifact.StreamingPhysicalState.packing.encode (stateValues state)) = state :=
  decoded_encode state

example (index : Fin 6039) (raw : Bool) :
    (ActualClockDAG.clockRoot index).eval (ActualClockDAG.network.value (fun _ => raw)) = raw :=
  ActualClockDAG.actual_positive index raw

example (index : Fin 6039) (raw : Bool) :
    (ActualClockDAG.resetRoot index).eval (ActualClockDAG.network.value (fun _ => raw)) = true :=
  ActualClockDAG.actual_inactive index raw

example (index : Fin %CTS%) (raw : Bool) :
    (ActualClockDAG.Inventory.ctsRoot index).eval (ActualClockDAG.network.value (fun _ => raw)) =
      (if ActualClockDAG.Inventory.ctsInverted index then !raw else raw) :=
  ActualClockDAG.Inventory.all_actual_cts_levels index raw

#check @Final.decoded_actual_step
#check @Final.actual_step_encoded
#check @Final.decoded_actual_observe
#check @Final.decoded_actual_run
#check @Final.decoded_physical_update
#check @encoded_decoded
#check @decoded_encode
#check @ActualClockDAG.actual_positive
#check @ActualClockDAG.actual_inactive
#check @ActualClockDAG.Inventory.all_actual_cts_levels

end Pinwheel.Artifact.StreamingPhysicalGRT.Required
'''
    return {'PhysicalGRTFinalRequired': text.replace('%CTS%', str(cts_count))}
