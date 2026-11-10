import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHI_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5298)
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
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__4 is_unsigned) ) : SailM Int )
          let w__5 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5299) ()) ) : SailM Bool )
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do (asl_Int w__6 is_unsigned) ) : SailM Int )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == element2)
                | .Cmp_NE => (element1 != element2)
                | .Cmp_GE => (element1 ≥b element2)
                | .Cmp_LT => (element1 <b element2)
                | .Cmp_GT => (element1 >b element2)
                | .Cmp_LE => (element1 ≤b element2)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__12 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECP_R_P_R__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  (X_set dn 64 (BitVec.subInt operand1 count))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCP_R_P_R__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  (X_set dn 64 (BitVec.addInt operand1 count))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 32 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCP_R_P_R_UW (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5300)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element +i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 32 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCP_R_P_R_SX (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5301)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element +i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 64 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5302)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element +i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 64 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5303)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element +i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 32 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECP_R_P_R_UW (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5304)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element -i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 32 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECP_R_P_R_SX (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5305)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element -i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 64 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5306)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element -i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize
  = 64 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5307)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let element ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element -i count) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__1 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__1)


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5308)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.subInt w__1 count)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5309)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt w__1 count)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5310)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element +i count) esize
              is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5311)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element +i count) esize
              is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
