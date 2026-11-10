/- Copyright (c) 2026 Crocodile Labs Inc.
SPDX-License-Identifier: Apache-2.0 -/
/-!
# Abstract real numbers for Sail models

Sail's `real` is an abstract carrier `R` with a `SailReal R` instance. Generated models are
parametric over the instance (the backend emits `variable {real : Type} [Sail.SailReal real]`
in every function module), so definitions and theorems about the model hold for every instance.
The laws are a separate `Prop` class, `SailReal.Laws`, which theorems take as a hypothesis.

* No `Float` (unsound) and no Mathlib: the spec only needs this interface.
* `Sail.AbstractRealRat` gives the computable exact-rational instance (core `Rat`), used where
  Isla parity is needed (Isla also evaluates reals as exact rationals).
* Division is total with `x / 0 = 0` (the Rat/Mathlib convention); the Arm model guards its
  divisions, so the junk value is never observed by well-formed executions.
* `sqrt?` is a *partial* exact square root: `some y` only when `y * y = x` exactly. There is no
  approximating square root: the model-facing `sqrt_real` demands a proof that the root is exact
  (mirroring Isla's `RealInexact` failure), so an inexact root cannot be computed silently.
-/

namespace Sail

/-- The original left-associated Sail natural-power recurrence. -/
def realNpowSpec {R : Type} (mul : R → R → R) (one x : R) : Nat → R
  | 0 => one
  | n + 1 => mul (realNpowSpec mul one x n) x

/-- Operations of an abstract real carrier. `R` is an `outParam`: in a context with a local
`[SailReal real]` (every generated module) the carrier is always that local one. -/
class SailReal (R : outParam Type) where
  ofInt : Int → R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  /-- Total inverse, `inv 0 = 0`. -/
  inv : R → R
  /-- Greatest integer `≤ x`. -/
  floor : R → Int
  le : R → R → Bool
  lt : R → R → Bool
  beq : R → R → Bool
  /-- Exact square root, `none` when the root is not representable exactly. -/
  sqrt? : R → Option R
  /-- An accelerated implementation must prove equality to the original recurrence.
      The default works for every carrier, even without field laws. -/
  powNat : { f : R → Nat → R // ∀ x n, f x n = realNpowSpec mul (ofInt 1) x n } :=
    ⟨realNpowSpec mul (ofInt 1), by intros; rfl⟩

namespace SailReal

variable {R : Type} [SailReal R]

@[reducible] def zero : R := ofInt 0
@[reducible] def one : R := ofInt 1
@[reducible] def sub (x y : R) : R := add x (neg y)
@[reducible] def div (x y : R) : R := mul x (inv y)
/-- Least integer `≥ x`. -/
@[reducible] def ceil (x : R) : Int := - floor (neg x)
@[reducible] def abs (x : R) : R := if lt x zero then neg x else x
/-- `x ^ n` for natural `n`. -/
def npow (x : R) (n : Nat) : R := SailReal.powNat.val x n

/-- No law or new premise is needed: every implementation carries its equality proof. -/
theorem npow_eq_spec (x : R) (n : Nat) :
    npow x n = realNpowSpec mul one x n :=
  SailReal.powNat.property x n
/-- `x ^ n` for integer `n`; `x ^ (-n) = inv (x ^ n)` (Sail `pow_real`). -/
def zpow (x : R) : Int → R
  | .ofNat n => npow x n
  | .negSucc n => inv (npow x (n + 1))

/-- The laws of an ordered field with floor and an exact partial square root. Theorems about a
generated model that depend on real arithmetic take `[SailReal.Laws R]` as a hypothesis. -/
class Laws (R : Type) [SailReal R] : Prop where
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  add_zero : ∀ a : R, add a zero = a
  add_neg : ∀ a : R, add a (neg a) = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  mul_one : ∀ a : R, mul a one = a
  mul_add : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : (zero : R) ≠ one
  mul_inv : ∀ a : R, a ≠ zero → mul a (inv a) = one
  inv_zero : inv (zero : R) = zero
  ofInt_add : ∀ m n : Int, ofInt (m + n) = add (ofInt m) (ofInt n : R)
  ofInt_mul : ∀ m n : Int, ofInt (m * n) = mul (ofInt m) (ofInt n : R)
  le_refl : ∀ a : R, le a a = true
  le_trans : ∀ a b c : R, le a b = true → le b c = true → le a c = true
  le_antisymm : ∀ a b : R, le a b = true → le b a = true → a = b
  le_total : ∀ a b : R, le a b = true ∨ le b a = true
  add_le_add_left : ∀ a b c : R, le a b = true → le (add c a) (add c b) = true
  mul_nonneg : ∀ a b : R, le zero a = true → le zero b = true → le zero (mul a b) = true
  lt_iff : ∀ a b : R, lt a b = (le a b && !le b a)
  beq_iff : ∀ a b : R, beq a b = true ↔ a = b
  floor_le : ∀ x : R, le (ofInt (floor x)) x = true
  lt_floor_add_one : ∀ x : R, lt x (ofInt (floor x + 1)) = true
  sqrt?_sound : ∀ x y : R, sqrt? x = some y → le zero y = true ∧ mul y y = x

end SailReal

end Sail
