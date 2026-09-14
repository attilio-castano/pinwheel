import Pinwheel.Binary.Records

namespace Pinwheel.Binary
open Engine.Reactive
open Engine.Reactive.Counted

attribute [local simp] List.append_assoc Bind.bind Pure.pure Functor.map
  StateT.bind StateT.pure StateT.map fin_law bits_law bool_law

theorem pins_law (value : Pins) (rest : List Byte) :
    getPins (putPins value ++ rest) = some (value, rest) := by
  cases value <;> simp [putPins, getPins]
  done

attribute [local simp] pins_law

theorem index_law (value : Index) (rest : List Byte) :
    getIndex (putIndex value ++ rest) = some (value, rest) := by
  cases value <;> simp [putIndex, getIndex]
  done

attribute [local simp] index_law

theorem serial_law (value : Serial) (rest : List Byte) :
    getSerial (putSerial value ++ rest) = some (value, rest) := by
  cases value <;> simp [putSerial, getSerial]
  done

attribute [local simp] serial_law

theorem pin_expr_law (value : PinExpr) (rest : List Byte) :
    getPinExpr (putPinExpr value ++ rest) = some (value, rest) := by
  cases value <;> simp [putPinExpr, getPinExpr]
  done

attribute [local simp] pin_expr_law

theorem sample_law (value : Sample) (rest : List Byte) :
    getSample (putSample value ++ rest) = some (value, rest) := by
  cases value <;> simp [putSample, getSample]
  done

attribute [local simp] sample_law

theorem condition_law (value : Condition) (rest : List Byte) :
    getCondition (putCondition value ++ rest) = some (value, rest) := by
  cases value <;> simp [putCondition, getCondition]
  done

attribute [local simp] condition_law

theorem check_law (value : Check) (rest : List Byte) :
    getCheck (putCheck value ++ rest) = some (value, rest) := by
  cases value <;> simp [putCheck, getCheck]
  done

attribute [local simp] check_law

theorem target_law (value : Target) (rest : List Byte) :
    getTarget (putTarget value ++ rest) = some (value, rest) := by
  cases value <;> simp [putTarget, getTarget]
  done

attribute [local simp] target_law

theorem transfer_law (value : Transfer) (rest : List Byte) :
    getTransfer (putTransfer value ++ rest) = some (value, rest) := by
  cases value <;> simp [putTransfer, getTransfer]
  done

attribute [local simp] transfer_law

theorem successor_law (value : Successor) (rest : List Byte) :
    getSuccessor (putSuccessor value ++ rest) = some (value, rest) := by
  cases value <;> simp [putSuccessor, getSuccessor]
  done

attribute [local simp] successor_law

theorem sample_option_law (value : Option Sample) (rest : List Byte) :
    getOption getSample (putOption putSample value ++ rest) = some (value, rest) := by
  exact option_law putSample getSample sample_law value rest
  done

attribute [local simp] sample_option_law

theorem template_law (value : Template) (rest : List Byte) :
    getTemplate (putTemplate value ++ rest) = some (value, rest) := by
  cases value <;> simp [putTemplate, getTemplate, show (3 : Fin 5).val = 3 from rfl]
  done

end Pinwheel.Binary
