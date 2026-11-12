import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071

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

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, k_op3_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (FPNeg element3))
            else (pure (element3)) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd element3 element1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, k_op3_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (FPNeg element3))
            else (pure (element3)) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd element3 element1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5125)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPMul element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, k_op3_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (FPNeg element3))
            else (pure (element3)) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd element3 element1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, k_op3_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (FPNeg element3))
            else (pure (element3)) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd element3 element1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FADDP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5126)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5127)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:8726.53-8726.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPAdd element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5128)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5129)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:8804.53-8804.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMaxNum element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5130)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5131)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:8882.53-8882.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMax element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5132)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5133)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:8960.53-8960.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMinNum element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5134)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5135)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:9038.53-9038.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMin element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n
  ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5136)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
