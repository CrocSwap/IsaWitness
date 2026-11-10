import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0118
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0582
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5746) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5747) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5748) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5749) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 >b w__2) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≥b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHS_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5750) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 >b w__2) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≥b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5751) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 >b w__2) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≥b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5752) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 >b w__2) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≥b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale :
  Nat, k_stream : Bool, scale = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5829) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64)))
    else (pure (base)) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        let _ : Unit :=
          if (w__4 : Bool)
          then
            (let eoff : Int := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
            (Hint_Prefetch addr pref_hint level stream))
          else ()
        (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale :
  Nat, k_stream : Bool, scale = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5830) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64)))
    else (pure (base)) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        let _ : Unit :=
          if (w__4 : Bool)
          then
            (let eoff : Int := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
            (Hint_Prefetch addr pref_hint level stream))
          else ()
        (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale :
  Nat, k_stream : Bool, scale = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5831) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64)))
    else (pure (base)) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        let _ : Unit :=
          if (w__4 : Bool)
          then
            (let eoff : Int := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
            (Hint_Prefetch addr pref_hint level stream))
          else ()
        (pure (()))
    (pure loop_vars))


end ArmFull.Functions
