import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0019
import ArmFull.Fn.M0063
import ArmFull.Fn.M0099
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open BarrierExt
open Barrier
open ArchVersion
open AccessType
open ATAccess

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VPADDL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3579)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3580)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_int_at (← occLabel 3581) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let h : Int := (fdiv_int elements 2)
  let (op1, op2, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, result) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (h -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, result)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, result) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 (2 *i e) esize)) )
                  : SailM (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 ((2 *i e) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let w__4 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let w__5 ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
                let result : Int := ((w__4 +i w__5) : Int)
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e
                    (Sail.Int.toNatChecked ((2 *i esize)))
                    (Sail.BitVec.castWidth (integer_subrange result ((2 *i esize) -i 1) 0)))) ) :
                  SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, op2, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × Int) )
  (pure (()))


/-- Type quantifiers: d : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, k_maximum
  : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPMAX_i_Op_A_txt (d : Nat) (elements : Int) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let op1 ← (( do (undefined_int_at (← occLabel 3585) ()) ) : SailM Int )
  let op2 ← (( do (undefined_int_at (← occLabel 3586) ()) ) : SailM Int )
  let result ← (( do (undefined_int_at (← occLabel 3587) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector_at (← occLabel 3588) 64) ) : SailM (BitVec 64) )
  let h : Int := (fdiv_int elements 2)
  let (dest, op1, op2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (h -i 1)
    (do
      let mut loop_vars := (dest, op1, op2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dest, op1, op2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let op1 : Int := (w__2 : Int)
          let w__3 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 ((2 *i e) +i 1) esize)) )
            : SailM (BitVec esize) )
          let w__5 ← (( do (asl_Int w__4 is_unsigned) ) : SailM Int )
          let op2 : Int := (w__5 : Int)
          let result : Int :=
            if (maximum : Bool)
            then (Max.max op1 op2)
            else (Min.min op1 op2)
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set dest e esize
              (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
            (BitVec 64) )
          let dest := (w__6 : (BitVec 64))
          let w__7 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let w__9 ← (( do (asl_Int w__8 is_unsigned) ) : SailM Int )
          let op1 : Int := (w__9 : Int)
          let w__10 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__11 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__10 ((2 *i e) +i 1) esize))
            ) : SailM (BitVec esize) )
          let w__12 ← (( do (asl_Int w__11 is_unsigned) ) : SailM Int )
          let op2 : Int := (w__12 : Int)
          let result : Int :=
            if (maximum : Bool)
            then (Max.max op1 op2)
            else (Min.min op1 op2)
          let w__13 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set dest (e +i h) esize
              (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
            (BitVec 64) )
          let dest := (w__13 : (BitVec 64))
          (pure ((dest, op1, op2, result)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × Int × Int × Int) )
  (D_set d dest)


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs
  [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQABS_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3589) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let result : Int := ((Int.natAbs (BitVec.toInt w__1)) : Int)
                let sat ← (( do (undefined_bool_at (← occLabel 3590) ()) ) : SailM Bool )
                let (__tup_0, __tup_1) ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ result esize))
                  ) : SailM ((BitVec esize) × Bool) )
                let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__2 e esize
                    (Sail.BitVec.castWidth __tup_0))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__3)
                let sat : Bool := __tup_1
                if (sat : Bool)
                then
                  (do
                    let w__4 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__4 1#1)))
                else (pure (()))
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQADD_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let sum ← (( do (undefined_int_at (← occLabel 3591) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let sum ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := sum
      for r in [loop_r_lower:loop_r_upper:1]i do
        let sum := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := sum
            for e in [loop_e_lower:loop_e_upper:1]i do
              let sum := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (asl_Int w__4 is_unsigned) ) : SailM Int )
                let sum : Int := ((w__2 +i w__5) : Int)
                let sat ← (( do (undefined_bool_at (← occLabel 3592) ()) ) : SailM Bool )
                let (__tup_0, __tup_1) ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ sum esize
                    is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth __tup_0))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                let sat : Bool := __tup_1
                if (sat : Bool)
                then
                  (do
                    let w__8 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__8 1#1)))
                else (pure (()))
                (pure (sum))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n
  : Nat, k_scalar_form : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMLAL_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3593) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3594)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat1 ← (( do (undefined_bool_at (← occLabel 3595) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3596) ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, product, sat1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (op1, op2, product, sat1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (op1, op2, product, sat1) := loop_vars
        loop_vars ← do
          let op2 ← (( do
            if ((! scalar_form) : Bool)
            then
              (do
                let w__2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 : Int := ((BitVec.toInt w__3) : Int)
                (pure (op2)))
            else (pure (op2)) ) : SailM Int )
          let w__4 ← (( do (Din_read n) ) : SailM (BitVec 64) )
          let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
            (BitVec esize) )
          let op1 : Int := ((BitVec.toInt w__5) : Int)
          let w__6 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ ((2 *i op1) *i op2)
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__6 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          let result ← (( do (undefined_int_at (← occLabel 3597) ()) ) : SailM Int )
          let result ← (( do
            if (add : Bool)
            then
              (do
                let w__7 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let result : Int := (((BitVec.toInt w__8) +i (BitVec.toInt product)) : Int)
                (pure (result)))
            else
              (do
                let w__9 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                let w__10 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__9 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let result : Int := (((BitVec.toInt w__10) -i (BitVec.toInt product)) : Int)
                (pure (result))) ) : SailM Int )
          let result : Int := result
          let sat2 ← (( do (undefined_bool_at (← occLabel 3598) ()) ) : SailM Bool )
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ result
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let w__11 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__12 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__11 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth __tup_0))) ) : SailM (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__12)
          let sat2 : Bool := __tup_1
          if ((sat1 || sat2) : Bool)
          then
            (do
              let w__13 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
              (FPSCR_write (_update_FPSCR_Type_QC w__13 1#1)))
          else (pure (()))
          (pure ((op1, op2, product, sat1)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec (2 * esize)) × Bool) )
  (pure (()))


/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n
  : Nat, k_scalar_form : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMLSL_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3607) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3608)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat1 ← (( do (undefined_bool_at (← occLabel 3609) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3610) ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, product, sat1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (op1, op2, product, sat1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (op1, op2, product, sat1) := loop_vars
        loop_vars ← do
          let op2 ← (( do
            if ((! scalar_form) : Bool)
            then
              (do
                let w__2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 : Int := ((BitVec.toInt w__3) : Int)
                (pure (op2)))
            else (pure (op2)) ) : SailM Int )
          let w__4 ← (( do (Din_read n) ) : SailM (BitVec 64) )
          let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
            (BitVec esize) )
          let op1 : Int := ((BitVec.toInt w__5) : Int)
          let w__6 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ ((2 *i op1) *i op2)
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__6 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          let result ← (( do (undefined_int_at (← occLabel 3611) ()) ) : SailM Int )
          let result ← (( do
            if (add : Bool)
            then
              (do
                let w__7 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let result : Int := (((BitVec.toInt w__8) +i (BitVec.toInt product)) : Int)
                (pure (result)))
            else
              (do
                let w__9 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                let w__10 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__9 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let result : Int := (((BitVec.toInt w__10) -i (BitVec.toInt product)) : Int)
                (pure (result))) ) : SailM Int )
          let result : Int := result
          let sat2 ← (( do (undefined_bool_at (← occLabel 3612) ()) ) : SailM Bool )
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ result
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let w__11 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__12 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__11 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth __tup_0))) ) : SailM (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__12)
          let sat2 : Bool := __tup_1
          if ((sat1 || sat2) : Bool)
          then
            (do
              let w__13 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
              (FPSCR_write (_update_FPSCR_Type_QC w__13 1#1)))
          else (pure (()))
          (pure ((op1, op2, product, sat1)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec (2 * esize)) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs
  : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMULH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3621) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3622)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3623) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3624) ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, result, sat) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, result, sat)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, result, sat) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, result, sat)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, result, sat) := loop_vars_1
              loop_vars_1 ← do
                let op2 ← (( do
                  if ((! scalar_form) : Bool)
                  then
                    (do
                      let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                      let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) :
                        SailM (BitVec esize) )
                      let op2 : Int := ((BitVec.toInt w__3) : Int)
                      (pure (op2)))
                  else (pure (op2)) ) : SailM Int )
                let w__4 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 : Int := ((BitVec.toInt w__5) : Int)
                let w__6 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
                    (Int.shiftr ((2 *i op1) *i op2) esize) esize)) ) : SailM
                  ((BitVec esize) × Bool) )
                let (tup__0, tup__1) := (w__6 : ((BitVec esize) × Bool))
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__8)
                if (sat : Bool)
                then
                  (do
                    let w__9 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__9 1#1)))
                else (pure (()))
                (pure ((op1, op2, result, sat)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, k_scalar_form
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMULL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3633) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3634)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool_at (← occLabel 3635) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3636) ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, product, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (op1, op2, product, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (op1, op2, product, sat) := loop_vars
        loop_vars ← do
          let op2 ← (( do
            if ((! scalar_form) : Bool)
            then
              (do
                let w__2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 : Int := ((BitVec.toInt w__3) : Int)
                (pure (op2)))
            else (pure (op2)) ) : SailM Int )
          let w__4 ← (( do (Din_read n) ) : SailM (BitVec 64) )
          let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
            (BitVec esize) )
          let op1 : Int := ((BitVec.toInt w__5) : Int)
          let w__6 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ ((2 *i op1) *i op2)
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__6 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat : Bool := tup__1
          let w__7 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__8 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth product))) ) : SailM (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__8)
          if (sat : Bool)
          then
            (do
              let w__9 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
              (FPSCR_write (_update_FPSCR_Type_QC w__9 1#1)))
          else (pure (()))
          (pure ((op1, op2, product, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec (2 * esize)) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Int, esize : Nat, m : Nat, k_src_unsigned
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQMOVN_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Int) (esize : Nat) (m : Nat) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int_at (← occLabel 3645) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let operand ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := operand
      for e in [loop_e_lower:loop_e_upper:1]i do
        let operand := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (asl_Int w__1 src_unsigned) ) : SailM Int )
          let operand : Int := (w__2 : Int)
          let sat ← (( do (undefined_bool_at (← occLabel 3646) ()) ) : SailM Bool )
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ operand esize
              dest_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          let w__3 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e esize (Sail.BitVec.castWidth __tup_0))) )
            : SailM (BitVec 64) )
          (D_set d w__4)
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__5 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
              (FPSCR_write (_update_FPSCR_Type_QC w__5 1#1)))
          else (pure (()))
          (pure (operand))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs
  [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQNEG_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3647) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let result : Int := ((Neg.neg (BitVec.toInt w__1)) : Int)
                let sat ← (( do (undefined_bool_at (← occLabel 3648) ()) ) : SailM Bool )
                let (__tup_0, __tup_1) ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ result esize))
                  ) : SailM ((BitVec esize) × Bool) )
                let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__2 e esize
                    (Sail.BitVec.castWidth __tup_0))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__3)
                let sat : Bool := __tup_1
                if (sat : Bool)
                then
                  (do
                    let w__4 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__4 1#1)))
                else (pure (()))
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


end ArmFull.Functions
