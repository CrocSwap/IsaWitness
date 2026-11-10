/- Copyright (c) 2026 Crocodile Labs Inc.
SPDX-License-Identifier: Apache-2.0 -/
import Sail.AbstractReal

/-!
# Exact-rational instance of `SailReal` (computable, core `Rat`; no Mathlib)

Not imported by the `Sail` umbrella: generated models never see a concrete instance, so they stay
parametric. Import this module to evaluate a model (or compare with Isla) on exact rationals.
-/

namespace Sail

/-- Exact square root of a rational: `√(n/d) = √n/√d` when numerator and denominator are both
perfect squares, otherwise `none`. The candidate is checked (`y * y = x`), so soundness holds by
construction. -/
def ratSqrt? (x : Rat) : Option Rat :=
  if x < 0 then none else
    let y : Rat := mkRat (Nat.sqrt x.num.toNat) (Nat.sqrt x.den)
    if 0 ≤ y ∧ y * y = x then some y else none

instance instSailRealRat : SailReal Rat where
  ofInt n := (n : Rat)
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  inv := (·⁻¹)
  floor := Rat.floor
  le a b := decide (a ≤ b)
  lt a b := decide (a < b)
  beq a b := decide (a = b)
  sqrt? := ratSqrt?
  powNat := ⟨fun x n => x ^ n, by
    intro x n
    induction n with
    | zero => simp [realNpowSpec]
    | succ n ih =>
      simpa only [realNpowSpec, Rat.pow_succ] using congrArg (fun y : Rat => y * x) ih⟩

namespace SailReal

theorem ratSqrt?_sound (x y : Rat) (h : ratSqrt? x = some y) : 0 ≤ y ∧ y * y = x := by
  unfold ratSqrt? at h
  split at h
  · cases h
  · simp only at h
    split at h
    · rename_i hy; cases h; exact hy
    · cases h

/-! Unfolding lemmas: the `SailReal Rat` operations are the core `Rat` ones. -/
@[simp] theorem rat_npow (x : Rat) (n : Nat) : npow x n = x ^ n := rfl

@[simp] theorem rat_ofInt (n : Int) : (ofInt n : Rat) = (n : Rat) := rfl
@[simp] theorem rat_zero : (zero : Rat) = 0 := rfl
@[simp] theorem rat_one : (one : Rat) = 1 := rfl
@[simp] theorem rat_add (a b : Rat) : add a b = a + b := rfl
@[simp] theorem rat_neg (a : Rat) : neg a = -a := rfl
@[simp] theorem rat_mul (a b : Rat) : mul a b = a * b := rfl
@[simp] theorem rat_inv (a : Rat) : inv a = a⁻¹ := rfl
@[simp] theorem rat_floor (a : Rat) : floor a = a.floor := rfl
@[simp] theorem rat_le (a b : Rat) : le a b = decide (a ≤ b) := rfl
@[simp] theorem rat_lt (a b : Rat) : lt a b = decide (a < b) := rfl
@[simp] theorem rat_beq (a b : Rat) : beq a b = decide (a = b) := rfl
@[simp] theorem rat_sqrt? (a : Rat) : sqrt? a = ratSqrt? a := rfl

instance lawsRat : Laws Rat where
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  add_zero a := by simpa using Rat.add_zero a
  add_neg a := by simp [Rat.add_neg_cancel]
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  mul_one a := by simp
  mul_add := Rat.mul_add
  zero_ne_one := by simp
  mul_inv a h := by simpa using Rat.mul_inv_cancel a (by simpa using h)
  inv_zero := by simp
  ofInt_add m n := Rat.intCast_add m n
  ofInt_mul m n := Rat.intCast_mul m n
  le_refl a := by simp
  le_trans a b c h1 h2 := by simp only [rat_le, decide_eq_true_eq] at *; exact Rat.le_trans h1 h2
  le_antisymm a b h1 h2 := by simp only [rat_le, decide_eq_true_eq] at *; exact Rat.le_antisymm h1 h2
  le_total a b := by simp only [rat_le, decide_eq_true_eq]; exact Rat.le_total
  add_le_add_left a b c h := by
    simp only [rat_le, rat_add, decide_eq_true_eq] at *; exact Rat.add_le_add_left.mpr h
  mul_nonneg a b ha hb := by
    simp only [rat_le, rat_mul, rat_zero, decide_eq_true_eq] at *; exact Rat.mul_nonneg ha hb
  lt_iff a b := by
    simp only [rat_le, rat_lt]
    by_cases h : a < b
    · have h1 : ¬ b ≤ a := Rat.not_le.mpr h
      have h2 : a ≤ b := Rat.le_of_lt h
      simp [h, h1, h2]
    · have h1 : b ≤ a := Rat.not_lt.mp h
      simp [h, h1]
  beq_iff a b := by simp
  floor_le x := by simp only [rat_le, rat_ofInt, rat_floor, decide_eq_true_eq]; exact Rat.floor_le x
  lt_floor_add_one x := by
    simp only [rat_lt, rat_ofInt, rat_floor, decide_eq_true_eq]; exact Rat.lt_floor_add_one x
  sqrt?_sound x y h := by
    have := ratSqrt?_sound x y h
    simp only [rat_le, rat_mul, rat_zero, decide_eq_true_eq]
    exact this

end SailReal

end Sail
