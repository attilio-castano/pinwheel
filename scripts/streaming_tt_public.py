"""Opaque generic bridges for actual public-output cells.

The helpers keep a large concrete Network.value out of definitional equality.
Every connected-cell and endpoint premise is a structural fact discharged by
readback-generated kernel proofs; final public-output claims have no premises.
"""
from streaming_tt_graph import header


def local_sources(*, prefix='PhysicalGRT',
                  namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Join'):
    module = prefix + 'PublicLocal'
    source = header(['Pinwheel.Hardware.StreamingPhysical.Device',
                     'Pinwheel.Hardware.StreamingPhysical.Local'], namespace) + r'''

theorem public_value_connected (network : Network) (environment : Nat → Bool)
    (gate : Fin network.nodes) (term : Term)
    (connected : (network.node gate).term (fun wire => .wire wire false) = term) :
    network.value environment (network.inputs + gate.val) =
      term.eval (network.value environment) :=
  (Network.value_node network environment gate).trans
    ((Node.eval_term (network.node gate) (fun wire => .wire wire false)
      (network.value environment)).symm.trans
        (congrArg (Term.eval (network.value environment)) connected))

theorem public_value_mask (network : Network) (environment : Nat → Bool)
    (gate : Fin network.nodes) (source : Atom)
    (connected : (network.node gate).term (fun wire => .wire wire false) =
      .conj (.conj (.variable 0) (.variable 1)) source.term) :
    network.value environment (network.inputs + gate.val) =
      ((network.value environment 0 && network.value environment 1) &&
        source.eval (network.value environment)) := by
  simpa only [Term.eval, Atom.eval_term] using
    (public_value_connected network environment gate _ connected)

theorem public_observe_wire {inputs registers outputs : Nat}
    (device : Device inputs registers outputs) (network : Network)
    (same_network : device.network = network)
    (input : Fin inputs → Bool) (state : Fin registers → Bool)
    (index : Fin outputs) (wire : Nat)
    (connected : device.output index = .wire wire false) :
    device.observe input state index =
      network.value (Device.environment input state) wire := by
  rw [Device.observe, connected, same_network] <;> rfl

theorem public_observe_constant {inputs registers outputs : Nat}
    (device : Device inputs registers outputs)
    (input : Fin inputs → Bool) (state : Fin registers → Bool)
    (index : Fin outputs) (value : Bool)
    (connected : device.output index = .constant value) :
    device.observe input state index = value := by
  rw [Device.observe, connected] <;> rfl

theorem public_observe_mask {inputs registers outputs : Nat}
    (device : Device inputs registers outputs) (network : Network)
    (same_network : device.network = network)
    (input : Fin inputs → Bool) (state : Fin registers → Bool)
    (index : Fin outputs) (gate : Fin network.nodes) (source : Atom)
    (endpoint : device.output index = .wire (network.inputs + gate.val) false)
    (connected : (network.node gate).term (fun wire => .wire wire false) =
      .conj (.conj (.variable 0) (.variable 1)) source.term)
    (enable reset_n : Bool)
    (enable_root : network.value (Device.environment input state) 0 = enable)
    (reset_root : network.value (Device.environment input state) 1 = reset_n) :
    device.observe input state index =
      ((enable && reset_n) && source.eval
        (network.value (Device.environment input state))) :=
  (public_observe_wire device network same_network input state index _ endpoint).trans
    ((public_value_mask network (Device.environment input state) gate source connected).trans
      ((congrArg (fun left => (left && network.value
        (Device.environment input state) 1) && source.eval
          (network.value (Device.environment input state))) enable_root).trans
        (congrArg (fun right => (enable && right) && source.eval
          (network.value (Device.environment input state))) reset_root)))

end %NAMESPACE%
'''
    return {module: source.replace('%NAMESPACE%', namespace)}
