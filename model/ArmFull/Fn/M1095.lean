import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0150
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1077

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

def decode_aarch32_instrs_VRINTX_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding : FPRounding := FPRounding_TIEEVEN
  let exact : Bool := true
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VRINTX_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) rounding)


def decode_aarch32_instrs_VRINTX_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding : FPRounding := FPRounding_TIEEVEN
  let exact : Bool := true
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_VRINTX_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) rounding)


def decode_aarch32_instrs_VRINTX_vfp_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:45469.29-45469.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let exact : Bool := true
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3827) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3828) 0 31))) ) :
        SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VRINTX_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VRINTX_vfp_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let exact : Bool := true
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3829) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3830) 0 31))) ) :
        SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VRINTX_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VRINTZ_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding : FPRounding := FPRounding_ZERO
  let exact : Bool := false
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VRINTZ_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) rounding)


def decode_aarch32_instrs_VRINTZ_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding : FPRounding := FPRounding_ZERO
  let exact : Bool := false
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_VRINTZ_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) rounding)


def decode_aarch32_instrs_VRINTZ_vfp_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:45698.29-45698.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let rounding ← (( do
        if ((op == 1#1) : Bool)
        then (pure (FPRounding_ZERO))
        else
          (do
            let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            (FPRoundingMode w__1)) ) : SailM FPRounding )
      let exact : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3833) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3834) 0 31))) ) :
        SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VRINTZ_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (m)) rounding))
  else (pure (()))


def decode_aarch32_instrs_VRINTZ_vfp_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let rounding ← (( do
        if ((op == 1#1) : Bool)
        then (pure (FPRounding_ZERO))
        else
          (do
            let w__3 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            (FPRoundingMode w__3)) ) : SailM FPRounding )
      let exact : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3835) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3836) 0 31))) ) :
        SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VRINTZ_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (m)) rounding))
  else (pure (()))


def decode_aarch32_instrs_VJCVT_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46459.25-46459.26"
  let w__0 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((cond != 0b1110#4) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (Vd +++ D))
  let m : Int := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VJCVT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)))


def decode_aarch32_instrs_VJCVT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (Vd +++ D))
  let m : Int := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VJCVT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCMLA_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (rot : (BitVec 2)) : SailM Unit := do
  let d : Int := d__arg
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3854) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector_at (← occLabel 3855) 64) ) : SailM (BitVec 64) )
  let operand3 ← (( do (undefined_bitvector_at (← occLabel 3856) 64) ) : SailM (BitVec 64) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3857)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3858)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, operand3, result1, result2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, operand2, operand3, result1, result2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, operand2, operand3, result1, result2) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
          let operand2 := (w__1 : (BitVec 64))
          let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
          let operand3 := (w__2 : (BitVec 64))
          let (result1, result2) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := ((fdiv_int elements 2) -i 1)
            (do
              let mut loop_vars_1 := (result1, result2)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (result1, result2) := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3859)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3860)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3861)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element4 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3862)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let (element1, element2, element3, element4) ← (( do
                    match rot with
                    | 0b00 =>
                      (do
                        let w__3 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element1 := (w__3 : (BitVec esize))
                        let w__4 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element2 := (w__4 : (BitVec esize))
                        let w__5 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element3 := (w__5 : (BitVec esize))
                        let w__6 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element4 := (w__6 : (BitVec esize))
                        (pure ((element1, element2, element3, element4))))
                    | 0b01 =>
                      (do
                        let w__7 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let w__8 ← (( do (FPNeg w__7) ) : SailM (BitVec esize) )
                        let element1 := (w__8 : (BitVec esize))
                        let w__9 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element2 := (w__9 : (BitVec esize))
                        let w__10 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element3 := (w__10 : (BitVec esize))
                        let w__11 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element4 := (w__11 : (BitVec esize))
                        (pure ((element1, element2, element3, element4))))
                    | 0b10 =>
                      (do
                        let w__12 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let w__13 ← (( do (FPNeg w__12) ) : SailM (BitVec esize) )
                        let element1 := (w__13 : (BitVec esize))
                        let w__14 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element2 := (w__14 : (BitVec esize))
                        let w__15 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let w__16 ← (( do (FPNeg w__15) ) : SailM (BitVec esize) )
                        let element3 := (w__16 : (BitVec esize))
                        let w__17 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element4 := (w__17 : (BitVec esize))
                        (pure ((element1, element2, element3, element4))))
                    | _ =>
                      (do
                        let w__18 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element1 := (w__18 : (BitVec esize))
                        let w__19 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element2 := (w__19 : (BitVec esize))
                        let w__20 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let w__21 ← (( do (FPNeg w__20) ) : SailM (BitVec esize) )
                        let element3 := (w__21 : (BitVec esize))
                        let w__22 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element4 := (w__22 : (BitVec esize))
                        (pure ((element1, element2, element3, element4)))) ) : SailM
                    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
                  let element4 := element4
                  let element3 := element3
                  let element2 := element2
                  let element1 := element1
                  let w__23 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 (e *i 2) esize)) ) : SailM
                    (BitVec esize) )
                  let w__24 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__25 ← (( do (FPMulAdd w__23 element2 element1 w__24) ) : SailM
                    (BitVec esize) )
                  let result1 := (w__25 : (BitVec esize))
                  let w__26 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((e *i 2) +i 1) esize)) ) :
                    SailM (BitVec esize) )
                  let w__27 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__28 ← (( do (FPMulAdd w__26 element4 element3 w__27) ) : SailM
                    (BitVec esize) )
                  let result2 := (w__28 : (BitVec esize))
                  let w__29 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__30 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__29 (e *i 2) esize
                      (Sail.BitVec.castWidth result1))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__30)
                  let w__31 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__32 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__31 ((e *i 2) +i 1) esize
                      (Sail.BitVec.castWidth result2))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__32)
                  (pure ((result1, result2)))
              (pure loop_vars_1)) ) : SailM ((BitVec esize) × (BitVec esize)) )
          (pure ((operand1, operand2, operand3, result1, result2)))
      (pure loop_vars)) ) : SailM
    ((BitVec 64) × (BitVec 64) × (BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Nat, m : Nat, n : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1] ∧ List.elem esize [16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCMLA_idx_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (regs : Nat) (rot : (BitVec 2)) : SailM Unit := do
  let d : Int := d__arg
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3863) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector_at (← occLabel 3864) 64) ) : SailM (BitVec 64) )
  let operand3 ← (( do (undefined_bitvector_at (← occLabel 3865) 64) ) : SailM (BitVec 64) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3866)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3867)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, operand3, result1, result2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, operand2, operand3, result1, result2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, operand2, operand3, result1, result2) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (Din_read m) ) : SailM (BitVec 64) )
          let operand2 := (w__1 : (BitVec 64))
          let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
          let operand3 := (w__2 : (BitVec 64))
          let (result1, result2) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := ((fdiv_int elements 2) -i 1)
            (do
              let mut loop_vars_1 := (result1, result2)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (result1, result2) := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3868)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3869)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3870)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element4 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3871)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let (element1, element2, element3, element4) ← (( do
                    match rot with
                    | 0b00 =>
                      (do
                        let w__3 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element1 := (w__3 : (BitVec esize))
                        let w__4 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element2 := (w__4 : (BitVec esize))
                        let w__5 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1)
                            esize)) ) : SailM (BitVec esize) )
                        let element3 := (w__5 : (BitVec esize))
                        let w__6 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element4 := (w__6 : (BitVec esize))
                        (pure ((element1, element2, element3, element4))))
                    | 0b01 =>
                      (do
                        let w__7 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1)
                            esize)) ) : SailM (BitVec esize) )
                        let w__8 ← (( do (FPNeg w__7) ) : SailM (BitVec esize) )
                        let element1 := (w__8 : (BitVec esize))
                        let w__9 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element2 := (w__9 : (BitVec esize))
                        let w__10 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element3 := (w__10 : (BitVec esize))
                        let w__11 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element4 := (w__11 : (BitVec esize))
                        (pure ((element1, element2, element3, element4))))
                    | 0b10 =>
                      (do
                        let w__12 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let w__13 ← (( do (FPNeg w__12) ) : SailM (BitVec esize) )
                        let element1 := (w__13 : (BitVec esize))
                        let w__14 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element2 := (w__14 : (BitVec esize))
                        let w__15 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1)
                            esize)) ) : SailM (BitVec esize) )
                        let w__16 ← (( do (FPNeg w__15) ) : SailM (BitVec esize) )
                        let element3 := (w__16 : (BitVec esize))
                        let w__17 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element4 := (w__17 : (BitVec esize))
                        (pure ((element1, element2, element3, element4))))
                    | _ =>
                      (do
                        let w__18 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1)
                            esize)) ) : SailM (BitVec esize) )
                        let element1 := (w__18 : (BitVec esize))
                        let w__19 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element2 := (w__19 : (BitVec esize))
                        let w__20 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let w__21 ← (( do (FPNeg w__20) ) : SailM (BitVec esize) )
                        let element3 := (w__21 : (BitVec esize))
                        let w__22 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element4 := (w__22 : (BitVec esize))
                        (pure ((element1, element2, element3, element4)))) ) : SailM
                    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
                  let element4 := element4
                  let element3 := element3
                  let element2 := element2
                  let element1 := element1
                  let w__23 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 (e *i 2) esize)) ) : SailM
                    (BitVec esize) )
                  let w__24 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__25 ← (( do (FPMulAdd w__23 element2 element1 w__24) ) : SailM
                    (BitVec esize) )
                  let result1 := (w__25 : (BitVec esize))
                  let w__26 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((e *i 2) +i 1) esize)) ) :
                    SailM (BitVec esize) )
                  let w__27 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__28 ← (( do (FPMulAdd w__26 element4 element3 w__27) ) : SailM
                    (BitVec esize) )
                  let result2 := (w__28 : (BitVec esize))
                  let w__29 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__30 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__29 (e *i 2) esize
                      (Sail.BitVec.castWidth result1))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__30)
                  let w__31 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__32 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__31 ((e *i 2) +i 1) esize
                      (Sail.BitVec.castWidth result2))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__32)
                  (pure ((result1, result2)))
              (pure loop_vars_1)) ) : SailM ((BitVec esize) × (BitVec esize)) )
          (pure ((operand1, operand2, operand3, result1, result2)))
      (pure loop_vars)) ) : SailM
    ((BitVec 64) × (BitVec 64) × (BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (pure (()))


end ArmFull.Functions
