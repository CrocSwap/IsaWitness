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
import ArmFull.Fn.M0582
import ArmFull.Fn.M0840
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1044

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGT_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5076)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
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
              let res ← (( do (undefined_bool_at (← occLabel 5077) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6071.59-6071.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element1 element2 w__5))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6075.59-6075.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element1 element2 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6079.59-6079.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element1 element2 w__9))
                | .Cmp_UN =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6083.59-6083.60"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareUN element1 element2 w__11))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6087.59-6087.60"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element1 element2 w__13))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6091.59-6091.60"
                    let w__15 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element2 element1 w__15))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6095.59-6095.60"
                    let w__17 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element2 element1 w__17)) ) : SailM Bool )
              let res := res
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMEQ_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5078)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
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
              let res ← (( do (undefined_bool_at (← occLabel 5079) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6184.59-6184.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element1 element2 w__5))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6188.59-6188.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element1 element2 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6192.59-6192.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element1 element2 w__9))
                | .Cmp_UN =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6196.59-6196.60"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareUN element1 element2 w__11))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6200.59-6200.60"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element1 element2 w__13))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6204.59-6204.60"
                    let w__15 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element2 element1 w__15))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6208.59-6208.60"
                    let w__17 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element2 element1 w__17)) ) : SailM Bool )
              let res := res
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMNE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5080)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
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
              let res ← (( do (undefined_bool_at (← occLabel 5081) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6297.59-6297.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element1 element2 w__5))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6301.59-6301.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element1 element2 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6305.59-6305.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element1 element2 w__9))
                | .Cmp_UN =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6309.59-6309.60"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareUN element1 element2 w__11))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6313.59-6313.60"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element1 element2 w__13))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6317.59-6317.60"
                    let w__15 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element2 element1 w__15))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:6321.59-6321.60"
                    let w__17 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element2 element1 w__17)) ) : SailM Bool )
              let res := res
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FLOGB_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:10809.53-10809.54"
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (FPLogB element w__3) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__4)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FABS_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:33028.53-33028.54"
              let w__3 ← (( do (FPAbs element) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FNEG_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:33097.53-33097.54"
              let w__3 ← (( do (FPNeg element) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7303)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPToFixed element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7304)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPToFixed element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7305)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPToFixed element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7306)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPToFixed element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


end ArmFull.Functions
