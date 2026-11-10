import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
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

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5703)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5704) ()) ) : SailM Bool )
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
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHS_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5705)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5706) ()) ) : SailM Bool )
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
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGT_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5707)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5708) ()) ) : SailM Bool )
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
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5709)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5710) ()) ) : SailM Bool )
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
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5711)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5712)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5713)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5714)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTUN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5715)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5716)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toNat w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ index ∧
  index ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUPQ_Z_Zi__ (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5717)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5718)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (element, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((s *i elements) +i index) esize)) ) :
            SailM (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let w__1 ← (( do
            (Elem_set result s 128
              (Sail.BitVec.castWidth (BitVec.replicateBits element
                (Sail.Int.toNatChecked ((Int.ediv 128 esize)))))) ) : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec VL)) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, position : Int, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EXTQ_Z_ZI_Des (VL : Nat) (dn : Nat) (m : Nat) (position : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5720)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let w__1 ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let concat : (BitVec 256) := (w__0 +++ w__1)
          ArmFull.assert ((0 ≤b position) && ((position +i 127) <b 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:54880.67-54880.68"
          (Elem_set result s 128
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
              (Sail.Int.toNatChecked ((position +i 127))) (Sail.Int.toNatChecked (position)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
