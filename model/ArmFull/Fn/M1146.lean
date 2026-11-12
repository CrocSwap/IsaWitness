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
import ArmFull.Fn.M0175
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1087
import ArmFull.Fn.M1093

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

def decode_aarch32_instrs_VMUL_s_T1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let w__2 ← (( do
        if ((((F == 1#1) && (size == 0b01#2)) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := false
      let floating_point : Bool := (F == 1#1)
      let long_destination : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Int := 16
      let elements : Int := 2
      let m ← (( do (undefined_int_at (← occLabel 3544) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3545) ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Int := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int :=
            (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Int := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m : Int := m
      let index : Int := index
      let esize : Int := esize
      let elements : Int := elements
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:30160.175-30160.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMUL_s_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let floating_point : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Nat := 1
      let esize : Int := 16
      let elements : Int := 2
      let index ← (( do (undefined_int_at (← occLabel 3546) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3547) ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Int := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int :=
            (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Int := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m : Int := m
      let index : Int := index
      let esize : Int := esize
      let elements : Int := elements
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:30216.175-30216.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) regs is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VNMLA_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:30788.29-30788.30"
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
      let vtype : VFPNegMul :=
        if ((op == 1#1) : Bool)
        then VFPNegMul_VNMLA
        else VFPNegMul_VNMLS
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3562) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3563) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3564) 0 31))) ) :
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        vtype))
  else (pure (()))


def decode_aarch32_instrs_VNMLA_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:30852.29-30852.30"
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
      if (((size == 0b01#2) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let vtype : VFPNegMul := VFPNegMul_VNMUL
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3565) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3566) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3567) 0 31))) ) :
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        vtype))
  else (pure (()))


def decode_aarch32_instrs_VNMLA_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
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
      let vtype : VFPNegMul :=
        if ((op == 1#1) : Bool)
        then VFPNegMul_VNMLA
        else VFPNegMul_VNMLS
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3568) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3569) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3570) 0 31))) ) :
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        vtype))
  else (pure (()))


def decode_aarch32_instrs_VNMLA_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
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
      if (((size == 0b01#2) && (! (HaveFP16Ext ()))) : Bool)
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
      let vtype : VFPNegMul := VFPNegMul_VNMUL
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3571) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3572) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3573) 0 31))) ) :
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        vtype))
  else (pure (()))


def decode_aarch32_instrs_VPADD_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Q == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
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
      (execute_aarch32_instrs_VPADD_f_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VPADD_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Q == 1#1) : Bool)
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
      (execute_aarch32_instrs_VPADD_f_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VPMAX_f_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let maximum : Bool := (op == 0#1)
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
      (execute_aarch32_instrs_VPMAX_f_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VPMAX_f_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
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
      let maximum : Bool := (op == 0#1)
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
      (execute_aarch32_instrs_VPMAX_f_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))))
  else (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRECPS_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                (BitVec esize) )
              let w__5 ← (( do (FPRecipStep w__2 w__4) ) : SailM (BitVec esize) )
              let w__6 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize (Sail.BitVec.castWidth w__5)))
                ) : SailM (BitVec 64) )
              (D_set (d +i r) w__6)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSQRTS_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                (BitVec esize) )
              let w__5 ← (( do (FPRSqrtStep w__2 w__4) ) : SailM (BitVec esize) )
              let w__6 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize (Sail.BitVec.castWidth w__5)))
                ) : SailM (BitVec 64) )
              (D_set (d +i r) w__6)
          (pure loop_vars_1))
    (pure loop_vars))


end ArmFull.Functions
