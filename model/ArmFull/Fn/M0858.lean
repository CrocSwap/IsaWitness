import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
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

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤
  m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMULH_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5230)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let product : Int := (Int.shiftr (element1 *i element2) esize)
              (Elem_set result e esize
                (Sail.BitVec.castWidth (integer_subrange product (esize -i 1) 0))))
          else
            (do
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__6)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤
  m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMULH_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5231)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let product : Int := (Int.shiftr (element1 *i element2) esize)
              (Elem_set result e esize
                (Sail.BitVec.castWidth (integer_subrange product (esize -i 1) 0))))
          else
            (do
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__6)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELO_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5232)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5233) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5234)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5235) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5236)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5237) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5238)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5239) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5240)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5241) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 >b w__1) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≥b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHS_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5242)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5243) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 >b w__1) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≥b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGT_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5244)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5245) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 >b w__1) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≥b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5246)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5247) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 >b w__1) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≥b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
