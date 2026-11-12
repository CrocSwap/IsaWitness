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
import ArmFull.Fn.M1092
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

def decode_aarch32_instrs_VMLA_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool_at (← occLabel 3472) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3473) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3474) ()) ) : SailM Int )
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
      let regs : Int := regs
      let elements : Int := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let add : Bool := (op == 0#1)
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3475) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3476) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3477) 0 31))) ) :
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
      (execute_aarch32_instrs_VMLA_f_Op_A_txt add advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMLA_s_A1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := false
      let add : Bool := (op == 0#1)
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
      let m ← (( do (undefined_int_at (← occLabel 3484) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3485) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:27879.175-27879.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMLA_s_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let add : Bool := (op == 0#1)
      let floating_point : Bool := false
      let long_destination : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Nat := 1
      let esize : Int := 16
      let elements : Int := 2
      let m ← (( do (undefined_int_at (← occLabel 3486) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3487) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:27937.175-27937.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) regs is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMLA_s_T1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
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
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := false
      let add : Bool := (op == 0#1)
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
      let m ← (( do (undefined_int_at (← occLabel 3488) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3489) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:28000.175-28000.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMLA_s_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let add : Bool := (op == 0#1)
      let floating_point : Bool := false
      let long_destination : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Nat := 1
      let esize : Int := 16
      let elements : Int := 2
      let m ← (( do (undefined_int_at (← occLabel 3490) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3491) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:28058.175-28058.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) regs is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMUL_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMUL_f_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:29579.29-29579.30"
      let floating_point ← (( do (undefined_bool_at (← occLabel 3521) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3522) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3523) ()) ) : SailM Int )
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
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3524) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3525) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3526) 0 31))) ) :
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMUL_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__2 ← (( do
        if (((sz == 1#1) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMUL_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool_at (← occLabel 3527) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3528) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3529) ()) ) : SailM Int )
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
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3530) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3531) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3532) 0 31))) ) :
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMUL_s_A1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
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
      let m ← (( do (undefined_int_at (← occLabel 3540) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3541) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:30043.175-30043.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMUL_s_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let index ← (( do (undefined_int_at (← occLabel 3542) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3543) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "sail-arm/instrs32.sail:30099.175-30099.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (index)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) regs is_unsigned))
  else (pure (()))


end ArmFull.Functions
