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
import ArmFull.Fn.M1072

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

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FNMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5084)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6585.57-6585.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6589.57-6589.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6592.53-6592.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FNMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5085)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6676.57-6676.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6680.57-6680.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6683.53-6683.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FMAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5086)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6767.57-6767.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6771.57-6771.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6774.53-6774.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FMSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5087)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6858.57-6858.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6862.57-6862.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6865.53-6865.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FNMAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5088)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6949.57-6949.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6953.57-6953.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6956.53-6956.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FNMSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5089)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7040.57-7040.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7044.57-7044.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7047.53-7047.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADD_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5090)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7120.49-7120.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPAdd element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5091)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7181.49-7181.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPMul element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FSUB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5092)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7242.49-7242.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPSub element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRECPS_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5094)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7367.49-7367.50"
          let w__0 ← (( do (FPRecipStepFused element1 element2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRSQRTS_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5095)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7431.49-7431.50"
          let w__0 ← (( do (FPRSqrtStepFused element1 element2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
