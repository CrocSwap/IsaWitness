import Sail
import ArmFull.Defs

open Sail ConcurrencyInterfaceV1

namespace ArmFull

@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := PreSail.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := PreSail.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := PreSail.undefined_unit ()
abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := PreSail.undefined_bit ()
abbrev undefined_bool (_ : Unit) : SailM Bool := PreSail.undefined_bool ()
abbrev undefined_int (_ : Unit) : SailM Int := PreSail.undefined_int ()
abbrev undefined_range (low high : Int) : SailM Int := PreSail.undefined_range low high
abbrev undefined_nat (_ : Unit) : SailM Nat := PreSail.undefined_nat ()
abbrev undefined_string (_ : Unit) : SailM String := PreSail.undefined_string ()
abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := PreSail.undefined_bitvector n
abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := PreSail.internal_pick

/-! Fork: labelled choices (see `ChoiceLabel`). The backend emits `(.site n)` for single-draw sites,
`(← occLabel n)` for sites that may execute repeatedly, and `(ℓ.child i)` inside initialisers. -/
abbrev occLabel (n : Nat) : SailM ChoiceLabel := PreSail.occLabel n
abbrev undefined_bit_at (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 1) := PreSail.undefined_bit_at ℓ ()
abbrev undefined_bool_at (ℓ : ChoiceLabel) (_ : Unit) : SailM Bool := PreSail.undefined_bool_at ℓ ()
abbrev undefined_int_at (ℓ : ChoiceLabel) (_ : Unit) : SailM Int := PreSail.undefined_int_at ℓ ()
abbrev undefined_nat_at (ℓ : ChoiceLabel) (_ : Unit) : SailM Nat := PreSail.undefined_nat_at ℓ ()
abbrev undefined_string_at (ℓ : ChoiceLabel) (_ : Unit) : SailM String := PreSail.undefined_string_at ℓ ()
abbrev undefined_range_at (ℓ : ChoiceLabel) (low high : Int) : SailM Int := PreSail.undefined_range_at ℓ low high
abbrev undefined_bitvector_at (ℓ : ChoiceLabel) (n : Nat) : SailM (BitVec n) := PreSail.undefined_bitvector_at ℓ n
abbrev internal_pick_at {α : Type} (ℓ : ChoiceLabel) : List α → SailM α := PreSail.internal_pick_at ℓ

/-! Fork (structured registers): `Register.X : RegisterRef T` is the typed reference of register `X`
(a lens into the generated register file `Regs`); reads are total. -/
abbrev RegisterRef := Sail.ConcurrencyInterfaceV1.RegisterRef Regs

abbrev writeReg (reg : RegisterRef α) (v : α) : SailM PUnit := PreSail.writeReg reg v

/-- `elab_without_expected_type`: the value type comes from the register, so in `SailME` contexts the
read is lifted instead of unifying `SailM ?α` with `SailME ε T`. -/
@[elab_without_expected_type]
abbrev readReg (reg : RegisterRef α) : SailM α := PreSail.readReg reg

@[elab_without_expected_type]
abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := PreSail.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := PreSail.writeRegRef reg_ref a

@[elab_without_expected_type]
abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := PreSail.reg_deref reg_ref

abbrev assert (p : Bool) (s : String) : SailM Unit := PreSail.assert p s

namespace ConcurrencyInterfaceV1

open Sail.ConcurrencyInterfaceV1

abbrev sail_mem_write (req : Mem_write_request n vasize (BitVec pa_size) ts Arch.arch_ak) : SailM (Result (Option Bool) Arch.abort) :=
  PreSail.sail_mem_write req

abbrev write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    SailM Unit := PreSail.write_ram addr_size data_size _hex_ram addr value

abbrev sail_mem_read (req : Mem_read_request n vasize (BitVec pa_size) ts Arch.arch_ak) : SailM (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := PreSail.sail_mem_read req

abbrev read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : SailM (BitVec (8 * data_size)) := PreSail.read_ram addr_size data_size _hex_ram addr

/-! Fork (H3): every effect hook appends an `Event` to the state's event log (see `Event`). -/
abbrev logEvent (e : Event) : SailM Unit := PreSail.logEvent e
abbrev sail_barrier (b : Arch.barrier) : SailM Unit := PreSail.sail_barrier b
abbrev sail_barrier_ext {β : Type} [Repr β] (b : β) : SailM Unit := PreSail.sail_barrier_ext b
abbrev sail_cache_op (op : Arch.cache_op) : SailM Unit := PreSail.sail_cache_op op
abbrev sail_tlbi (op : Arch.tlb_op) : SailM Unit := PreSail.sail_tlbi op
abbrev sail_translation_start (ts : Arch.trans_start) : SailM Unit := PreSail.sail_translation_start ts
abbrev sail_translation_end (te : Arch.trans_end) : SailM Unit := PreSail.sail_translation_end te
abbrev sail_take_exception (f : Arch.fault) : SailM Unit := PreSail.sail_take_exception f
abbrev sail_return_exception (a : Arch.pa) : SailM Unit := PreSail.sail_return_exception a

end ConcurrencyInterfaceV1

abbrev cycle_count (a : Unit) : SailM Unit := PreSail.cycle_count a

abbrev get_cycle_count (a : Unit) : SailM Nat := PreSail.get_cycle_count a


abbrev print_effect (str : String) : SailM Unit := PreSail.print_effect str

abbrev print_int_effect (str : String) (n : Int) : SailM Unit := PreSail.print_int_effect str n

abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := PreSail.print_bits_effect str x

abbrev print_endline_effect (str : String) : SailM Unit := PreSail.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := PreSail.PreSailME.run m

def SailME.throw (e : α) : SailME α β := PreSail.PreSailME.throw e

abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := PreSail.sailTryCatchE e h

def unwrapValue [Inhabited α] (x : SailM α) : α :=
  match x.run default with
  | .ok x _ => x
  | _ => default

/-- Fork: running out of loop fuel is an error, never a silent loop exit. -/
def loopFuelExhausted (_ : Unit) : SailM α := throw (Sail.Error.FuelExhausted "loop")

/-- Fork: a fuel-indexed recursive function (one without a Sail termination measure) ran out of fuel; an error,
never a default value. -/
def recursionFuelExhausted (fn : String) : SailM α := throw (Sail.Error.FuelExhausted fn)

/-- Fork: fuel-bounded `while`; structural on `fuel`, so proofs can unfold it one iteration at a time. -/
def sailWhileFuelM [Monad m] [MonadLiftT SailM m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α) :
    m α :=
  match fuel with
  | 0 => monadLift (loopFuelExhausted () : SailM α)
  | n + 1 => do if ← cond init then sailWhileFuelM n cond (← f init) f else pure init

/-- Fork: fuel-bounded `repeat ... until`; exhausting the fuel is an error. -/
def sailUntilFuelM [Monad m] [MonadLiftT SailM m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α) :
    m α :=
  match fuel with
  | 0 => monadLift (loopFuelExhausted () : SailM α)
  | n + 1 => do
    let x ← f init
    if ← cond x then pure x else sailUntilFuelM n cond x f
