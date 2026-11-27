import PinwheelWitness.I2CRead

/-! Witnesses that conditional protocol theorems are not vacuous: concrete
scenarios that satisfy every hypothesis. They replay long executions in the
kernel, so they are kept out of the default `Pinwheel` build and checked by
`scripts/check-witness.py`. -/
