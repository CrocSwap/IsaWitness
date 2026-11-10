import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0150
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 :
  Nat, sel2 : Nat, sel2 = 1 ∧
  sel1 = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UADDLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5573)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let res : Int := (element1 +i element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 :
  Nat, sel2 : Nat, sel2 = 0 ∧
  sel1 = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USUBLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5574)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let res : Int := (element1 -i element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 :
  Nat, sel2 : Nat, sel2 = 1 ∧
  sel1 = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USUBLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5575)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let res : Int := (element1 -i element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 :
  Nat, sel2 : Nat, sel2 = 1 ∧
  sel1 = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDLBT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5576)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let res : Int := (element1 +i element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 :
  Nat, sel2 : Nat, sel2 = 1 ∧
  sel1 = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBLBT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5577)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let res : Int := (element1 -i element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 :
  Nat, sel2 : Nat, sel2 = 0 ∧
  sel1 = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBLTB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5578)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let res : Int := (element1 -i element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, k_sub_i : Bool, k_sub_r : Bool, 0
  ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CADD_Z_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5579)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let acc_r : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let acc_i : Int := (BitVec.toInt w__1)
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let elt2_r : Int := (BitVec.toInt w__2)
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let elt2_i : Int := (BitVec.toInt w__3)
          let (acc_i, acc_r) : (Int × Int) :=
            if (sub_i : Bool)
            then
              (let acc_r : Int := (acc_r -i elt2_i)
              let acc_i : Int := (acc_i +i elt2_r)
              (acc_i, acc_r))
            else (acc_i, acc_r)
          let (acc_i, acc_r) : (Int × Int) :=
            if (sub_r : Bool)
            then
              (let acc_r : Int := (acc_r +i elt2_i)
              let acc_i : Int := (acc_i -i elt2_r)
              (acc_i, acc_r))
            else (acc_i, acc_r)
          let acc_r : Int := acc_r
          let acc_i : Int := acc_i
          let w__4 ← (( do
            (Elem_set result ((2 *i p) +i 0) esize
              (Sail.BitVec.castWidth (integer_subrange acc_r (esize -i 1) 0))) ) : SailM (BitVec VL)
            )
          let result := (w__4 : (BitVec VL))
          (Elem_set result ((2 *i p) +i 1) esize
            (Sail.BitVec.castWidth (integer_subrange acc_i (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, k_sub_i : Bool, k_sub_r : Bool, 0
  ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQCADD_Z_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5580)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let acc_r : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let acc_i : Int := (BitVec.toInt w__1)
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let elt2_r : Int := (BitVec.toInt w__2)
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let elt2_i : Int := (BitVec.toInt w__3)
          let (acc_i, acc_r) : (Int × Int) :=
            if (sub_i : Bool)
            then
              (let acc_r : Int := (acc_r -i elt2_i)
              let acc_i : Int := (acc_i +i elt2_r)
              (acc_i, acc_r))
            else (acc_i, acc_r)
          let (acc_i, acc_r) : (Int × Int) :=
            if (sub_r : Bool)
            then
              (let acc_r : Int := (acc_r +i elt2_i)
              let acc_i : Int := (acc_i -i elt2_r)
              (acc_i, acc_r))
            else (acc_i, acc_r)
          let acc_r : Int := acc_r
          let acc_i : Int := acc_i
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat acc_r esize)) ) : SailM
            (BitVec esize) )
          let w__5 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__4)) )
            : SailM (BitVec VL) )
          let result := (w__5 : (BitVec VL))
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat acc_i esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__6))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i
  : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5581)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt1_a : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt2_a : Int := (BitVec.toInt w__1)
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i sel_b) esize)) ) : SailM
            (BitVec esize) )
          let elt2_b : Int := (BitVec.toInt w__2)
          let elt3_r ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let elt3_i ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let product_r : Int := (elt1_a *i elt2_a)
          let product_i : Int := (elt1_a *i elt2_b)
          let result ← (( do
            if (sub_r : Bool)
            then
              (do
                (Elem_set result ((2 *i p) +i 0) esize
                  (Sail.BitVec.castWidth (BitVec.subInt elt3_r product_r))))
            else
              (do
                (Elem_set result ((2 *i p) +i 0) esize
                  (Sail.BitVec.castWidth (BitVec.addInt elt3_r product_r)))) ) : SailM (BitVec VL) )
          if (sub_i : Bool)
          then
            (do
              (Elem_set result ((2 *i p) +i 1) esize
                (Sail.BitVec.castWidth (BitVec.subInt elt3_i product_i))))
          else
            (do
              (Elem_set result ((2 *i p) +i 1) esize
                (Sail.BitVec.castWidth (BitVec.addInt elt3_i product_i))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b
  : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let pairspersegment : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv 128 (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5582)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (p -i (Nat.mod (Sail.Int.toNatChecked (p)) pairspersegment))
          let s : Int := (segmentbase +i index)
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt1_a : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt2_a : Int := (BitVec.toInt w__1)
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_b) esize)) ) : SailM
            (BitVec esize) )
          let elt2_b : Int := (BitVec.toInt w__2)
          let elt3_r ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let elt3_i ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let product_r : Int := (elt1_a *i elt2_a)
          let product_i : Int := (elt1_a *i elt2_b)
          let result ← (( do
            if (sub_r : Bool)
            then
              (do
                (Elem_set result ((2 *i p) +i 0) esize
                  (Sail.BitVec.castWidth (BitVec.subInt elt3_r product_r))))
            else
              (do
                (Elem_set result ((2 *i p) +i 0) esize
                  (Sail.BitVec.castWidth (BitVec.addInt elt3_r product_r)))) ) : SailM (BitVec VL) )
          if (sub_i : Bool)
          then
            (do
              (Elem_set result ((2 *i p) +i 1) esize
                (Sail.BitVec.castWidth (BitVec.subInt elt3_i product_i))))
          else
            (do
              (Elem_set result ((2 *i p) +i 1) esize
                (Sail.BitVec.castWidth (BitVec.addInt elt3_i product_i))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b
  : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CMLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let pairspersegment : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv 128 (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5583)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (p -i (Nat.mod (Sail.Int.toNatChecked (p)) pairspersegment))
          let s : Int := (segmentbase +i index)
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt1_a : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt2_a : Int := (BitVec.toInt w__1)
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_b) esize)) ) : SailM
            (BitVec esize) )
          let elt2_b : Int := (BitVec.toInt w__2)
          let elt3_r ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let elt3_i ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let product_r : Int := (elt1_a *i elt2_a)
          let product_i : Int := (elt1_a *i elt2_b)
          let result ← (( do
            if (sub_r : Bool)
            then
              (do
                (Elem_set result ((2 *i p) +i 0) esize
                  (Sail.BitVec.castWidth (BitVec.subInt elt3_r product_r))))
            else
              (do
                (Elem_set result ((2 *i p) +i 0) esize
                  (Sail.BitVec.castWidth (BitVec.addInt elt3_r product_r)))) ) : SailM (BitVec VL) )
          if (sub_i : Bool)
          then
            (do
              (Elem_set result ((2 *i p) +i 1) esize
                (Sail.BitVec.castWidth (BitVec.subInt elt3_i product_i))))
          else
            (do
              (Elem_set result ((2 *i p) +i 1) esize
                (Sail.BitVec.castWidth (BitVec.addInt elt3_i product_i))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i
  : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDCMLAH_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5584)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let res_i ← (( do (undefined_int_at (← occLabel 5585) ()) ) : SailM Int )
  let res_r ← (( do (undefined_int_at (← occLabel 5586) ()) ) : SailM Int )
  let (res_i, res_r, result) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (res_i, res_r, result)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (res_i, res_r, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt1_a : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt2_a : Int := (BitVec.toInt w__1)
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i sel_b) esize)) ) : SailM
            (BitVec esize) )
          let elt2_b : Int := (BitVec.toInt w__2)
          let elt3_r ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let elt3_i ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let product_r : Int := (elt1_a *i elt2_a)
          let product_i : Int := (elt1_a *i elt2_b)
          let res_r : Int :=
            if (sub_r : Bool)
            then ((Int.shiftl (BitVec.toInt elt3_r) esize) -i (2 *i product_r))
            else ((Int.shiftl (BitVec.toInt elt3_r) esize) +i (2 *i product_r))
          let res_r : Int :=
            (Int.shiftr (res_r +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res_r esize)) ) : SailM
            (BitVec esize) )
          let w__4 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__3)) )
            : SailM (BitVec VL) )
          let result := (w__4 : (BitVec VL))
          let res_i : Int :=
            if (sub_i : Bool)
            then ((Int.shiftl (BitVec.toInt elt3_i) esize) -i (2 *i product_i))
            else ((Int.shiftl (BitVec.toInt elt3_i) esize) +i (2 *i product_i))
          let res_i : Int :=
            (Int.shiftr (res_i +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
          let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res_i esize)) ) : SailM
            (BitVec esize) )
          let w__6 ← (( do (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__5)) )
            : SailM (BitVec VL) )
          let result := (w__6 : (BitVec VL))
          (pure ((res_i, res_r, result)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
