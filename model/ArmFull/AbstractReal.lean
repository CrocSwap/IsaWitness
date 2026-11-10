import Sail
import ArmFull.Defs

/-!
Fork (`--lean-abstract-reals`, Doug B3): Sail `real` is an abstract carrier. Every generated
function module declares `variable {real : Type} [Sail.SailReal real]`, so the model is
parametric over the `SailReal` instance (`Sail.AbstractRealRat` gives exact rationals).
No `Float`, no Mathlib. `random_real` is deliberately absent (a pure Sail function cannot draw from
the choice oracle, and a constant would be unfaithful): a model that uses it fails to build.
-/

namespace ArmFull

open Sail Sail.SailReal

variable {R : Type} [SailReal R]

/-! Literals and arithmetic syntax for real literals emitted by the backend (`1/2`, `-3`). -/
scoped instance : OfNat R n := ⟨ofInt n⟩
scoped instance : Inhabited R := ⟨zero⟩
scoped instance : Neg R := ⟨neg⟩
scoped instance : Add R := ⟨add⟩
scoped instance : Sub R := ⟨sub⟩
scoped instance : Mul R := ⟨mul⟩
scoped instance : Div R := ⟨div⟩
/-- Fork (integration): Sail `!=`/`==` on reals print as `bne`/`==`; equality is the class `beq` (same as `eq_real`). -/
scoped instance : BEq R := ⟨beq⟩

-- val "neg_real" : real -> real
@[reducible] def neg_real (x : R) : R := neg x
-- val "mult_real" : (real, real) -> real
@[reducible] def mult_real (x y : R) : R := mul x y
-- val "sub_real" : (real, real) -> real
@[reducible] def sub_real (x y : R) : R := sub x y
-- val "add_real" : (real, real) -> real
@[reducible] def add_real (x y : R) : R := add x y
-- val "div_real" : (real, real) -> real   (total: `x / 0 = 0`)
@[reducible] def div_real (x y : R) : R := div x y
/-- val sqrt : real -> real, made monadic by the Lean splice (Doug, integration): the exact root when the
instance has one (`sqrt?` returns `some y` only when `y * y = x`), otherwise the `RealInexact` error
(Isla's `RealInexact`). Never an approximation, never a default. Full Arm: FPSqrt and RecipSqrtEstimate. -/
def sqrt_real (x : R) : SailM R :=
  match SailReal.sqrt? x with
  | some y => pure y
  | none => throw (Sail.Error.RealInexact "sqrt_real" : Sail.Error exception)
-- val "abs_real" : real -> real
@[reducible] def abs_real (x : R) : R := SailReal.abs x
-- val floor = pure "round_down" : real -> int
@[reducible] def round_down (x : R) : Int := floor x
-- val ceil = pure "round_up" : real -> int
@[reducible] def round_up (x : R) : Int := ceil x
-- val "to_real" : int -> real
@[reducible] def to_real (x : Int) : R := ofInt x
-- val "eq_real" : (real, real) -> bool
@[reducible] def eq_real (x y : R) : Bool := beq x y
-- val "lt_real" : (real, real) -> bool
@[reducible] def lt_real (x y : R) : Bool := lt x y
-- val "gt_real" : (real, real) -> bool
@[reducible] def gt_real (x y : R) : Bool := lt y x
-- val "lteq_real" : (real, real) -> bool
@[reducible] def lteq_real (x y : R) : Bool := le x y
-- val "gteq_real" : (real, real) -> bool
@[reducible] def gteq_real (x y : R) : Bool := le y x
-- val pow_real = pure "real_power" : (real, int) -> real
@[reducible] def real_power (x : R) (n : Int) : R := zpow x n
-- val "print_real" : (string, real) -> unit
def print_real (_ : String) (_ : R) : Unit := ()
-- val "prerr_real" : (string, real) -> unit
def prerr_real (_ : String) (_ : R) : Unit := ()

/-- Labelled undefined real: an oracle draw of a numerator (`ℓ.child 0`, any `Int`) and a
denominator (`ℓ.child 1`, any `Nat`, shifted by one), so the draw ranges over every rational of
the carrier. Never a constant. -/
def undefined_real_at (ℓ : Sail.ConcurrencyInterfaceV1.ChoiceLabel) (_ : Unit) : SailM R := do
  let n ← Sail.ConcurrencyInterfaceV1.PreSail.undefined_int_at (.child ℓ 0) ()
  let d ← Sail.ConcurrencyInterfaceV1.PreSail.undefined_nat_at (.child ℓ 1) ()
  pure (div (ofInt n) (ofInt (d + 1)))

end ArmFull
