import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0086
import ArmFull.Fn.M0099
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0175
import ArmFull.Fn.M1094
import ArmFull.Fn.M1095

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

def decode_aarch32_instrs_VSQRT_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:36850.29-36850.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3744) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3745) 0 31))) ) :
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
      (execute_aarch32_instrs_VSQRT_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VSQRT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let w__5 ← (( do
        if ((← do
             let w__3 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__3) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__4 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__4) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3746) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3747) 0 31))) ) :
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
      (execute_aarch32_instrs_VSQRT_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VSUB_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let advsimd : Bool := true
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match sz with
        | 0 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VSUB_f_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:39545.29-39545.30"
      let elements ← (( do (undefined_int_at (← occLabel 3756) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3757) ()) ) : SailM Int )
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3758) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3759) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3760) 0 31))) ) :
        SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n : Int := n
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VSUB_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((sz == 1#1) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let advsimd : Bool := true
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match sz with
        | 0 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VSUB_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let elements ← (( do (undefined_int_at (← occLabel 3761) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3762) ()) ) : SailM Int )
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__5 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3763) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3764) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3765) 0 31))) ) :
        SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n : Int := n
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMAXNM_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let maximum : Bool := (op == 0#1)
  let advsimd : Bool := true
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match sz with
    | 0 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VMAXNM_A2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let elements ← (( do (undefined_int_at (← occLabel 3809) ()) ) : SailM Int )
  let regs ← (( do (undefined_int_at (← occLabel 3810) ()) ) : SailM Int )
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let regs : Int := regs
  let elements : Int := elements
  let advsimd : Bool := false
  let maximum : Bool := (op == 0#1)
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3811) 0 31))) ) :
    SailM Nat )
  let n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3812) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3813) 0 31))) ) :
    SailM Nat )
  let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let n : Nat := (BitVec.toNat (N +++ Vn))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m, n))
    | _ => (d, esize, m, n)
  let n : Int := n
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VMAXNM_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let maximum : Bool := (op == 0#1)
  let advsimd : Bool := true
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match sz with
    | 0 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VMAXNM_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let elements ← (( do (undefined_int_at (← occLabel 3814) ()) ) : SailM Int )
  let regs ← (( do (undefined_int_at (← occLabel 3815) ()) ) : SailM Int )
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let regs : Int := regs
  let elements : Int := elements
  let advsimd : Bool := false
  let maximum : Bool := (op == 0#1)
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3816) 0 31))) ) :
    SailM Nat )
  let n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3817) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3818) 0 31))) ) :
    SailM Nat )
  let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let n : Nat := (BitVec.toNat (N +++ Vn))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m, n))
    | _ => (d, esize, m, n)
  let n : Int := n
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VCMLA_A1enc_A_txt (rot : (BitVec 2)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46581.41-46581.42"
  (execute_aarch32_instrs_VCMLA_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCMLA_T1enc_A_txt (rot : (BitVec 2)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46620.41-46620.42"
  (execute_aarch32_instrs_VCMLA_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCMLA_idx_A1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (rot : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int :=
    if ((S == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat Vm)
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let index : Int :=
    if ((S == 1#1) : Bool)
    then 0
    else (BitVec.toNat M)
  ArmFull.assert ((0 ≤b m) && ((m ≤b 31) && ((esize == 16) || (esize == 32)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46716.64-46716.65"
  (execute_aarch32_instrs_VCMLA_idx_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) rot)


end ArmFull.Functions
