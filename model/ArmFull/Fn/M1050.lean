import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0086
import ArmFull.Fn.M0099
import ArmFull.Fn.M0116
import ArmFull.Fn.M0124
import ArmFull.Fn.M0167
import ArmFull.Fn.M0175
import ArmFull.Fn.M1009

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

def decode_aarch32_instrs_VMOVX_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((! (HaveFP16Ext ())) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__2) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__3 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__3) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VMOVX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VINS_A1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((! (HaveFP16Ext ())) : Bool)
      then sailThrow ((Error_Undefined ()))
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
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VINS_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VINS_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((! (HaveFP16Ext ())) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__2) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__3 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__3) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VINS_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VMOV_d_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:28225.29-28225.30"
      let to_arm_registers : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let m : Int := (BitVec.toNat (M +++ Vm))
      if (((t == 15) || (t2 == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((to_arm_registers && (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_d_Op_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) to_arm_registers))
  else (pure (()))


def decode_aarch32_instrs_VMOV_d_T1enc_A_txt (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let to_arm_registers : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let m : Int := (BitVec.toNat (M +++ Vm))
      if (((t == 15) || (t2 == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((to_arm_registers && (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_d_Op_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) to_arm_registers))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_A1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3492) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (imm4H : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:28338.29-28338.30"
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
      let single_register : Bool := (size != 0b11#2)
      let advsimd : Bool := false
      let imm16 ← (( do (undefined_bitvector_at (← occLabel 3493) 16) ) : SailM (BitVec 16) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3494) 32) ) : SailM (BitVec 32) )
      let imm64 ← (( do (undefined_bitvector_at (← occLabel 3495) 64) ) : SailM (BitVec 64) )
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3496) 0 31))) ) :
        SailM Nat )
      let regs : Int := 1
      let (d, imm32, imm64, regs) ← (( do
        match size with
        | 0b01 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let imm16 ← (( do (VFPExpandImm (imm4H +++ imm4L) 16) ) : SailM (BitVec 16) )
            let imm32 : (BitVec 32) := ((Zeros (n := 16)) +++ imm16)
            (pure ((d, imm32, imm64, regs))))
        | 0b10 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let w__4 ← (( do (VFPExpandImm (imm4H +++ imm4L) 32) ) : SailM (BitVec 32) )
            let imm32 := (w__4 : (BitVec 32))
            (pure ((d, imm32, imm64, regs))))
        | 0b11 =>
          (do
            let d : Nat := (BitVec.toNat (D +++ Vd))
            let w__5 ← (( do (VFPExpandImm (imm4H +++ imm4L) 64) ) : SailM (BitVec 64) )
            let imm64 := (w__5 : (BitVec 64))
            let regs : Int := 1
            (pure ((d, imm32, imm64, regs))))
        | _ => (pure ((d, imm32, imm64, regs))) ) : SailM (Nat × (BitVec 32) × (BitVec 64) × Int)
        )
      let regs : Int := regs
      let d : Int := d
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_A3enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3497) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_A4enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3498) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_A5enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3499) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_T1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3500) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_T2enc_A_txt (D : (BitVec 1)) (imm4H : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm4L : (BitVec 4)) : SailM Unit := do
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
      let single_register : Bool := (size != 0b11#2)
      let advsimd : Bool := false
      let imm16 ← (( do (undefined_bitvector_at (← occLabel 3501) 16) ) : SailM (BitVec 16) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3502) 32) ) : SailM (BitVec 32) )
      let imm64 ← (( do (undefined_bitvector_at (← occLabel 3503) 64) ) : SailM (BitVec 64) )
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3504) 0 31))) ) :
        SailM Nat )
      let regs : Int := 1
      let (d, imm32, imm64, regs) ← (( do
        match size with
        | 0b01 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let imm16 ← (( do (VFPExpandImm (imm4H +++ imm4L) 16) ) : SailM (BitVec 16) )
            let imm32 : (BitVec 32) := ((Zeros (n := 16)) +++ imm16)
            (pure ((d, imm32, imm64, regs))))
        | 0b10 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let w__6 ← (( do (VFPExpandImm (imm4H +++ imm4L) 32) ) : SailM (BitVec 32) )
            let imm32 := (w__6 : (BitVec 32))
            (pure ((d, imm32, imm64, regs))))
        | 0b11 =>
          (do
            let d : Nat := (BitVec.toNat (D +++ Vd))
            let w__7 ← (( do (VFPExpandImm (imm4H +++ imm4L) 64) ) : SailM (BitVec 64) )
            let imm64 := (w__7 : (BitVec 64))
            let regs : Int := 1
            (pure ((d, imm32, imm64, regs))))
        | _ => (pure ((d, imm32, imm64, regs))) ) : SailM (Nat × (BitVec 32) × (BitVec 64) × Int)
        )
      let regs : Int := regs
      let d : Int := d
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_T3enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3505) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_T4enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3506) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_i_T5enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3507) 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               cmode 3 2)) != 0b11#2)) : Bool)
      then sailThrow ((Error_See "VORR (immediate)"))
      else (pure (()))
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) imm32 imm64
        (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOVL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm3H : (BitVec 3)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((imm3H == 0b000#3) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((imm3H != 0b001#3) && (imm3H != 0b010#3)) && (imm3H != 0b100#3)) : Bool)
      then sailThrow ((Error_See "VSHLL"))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (8 *i (BitVec.toNat imm3H))
      let is_unsigned : Bool := (U == 1#1)
      let elements : Int := (fdiv_int 64 esize)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMOVL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm3H : (BitVec 3)) (Vd : (BitVec 4)) (L : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((imm3H == 0b000#3) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((imm3H != 0b001#3) && (imm3H != 0b010#3)) && (imm3H != 0b100#3)) : Bool)
      then sailThrow ((Error_See "VSHLL"))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (8 *i (BitVec.toNat imm3H))
      let is_unsigned : Bool := (U == 1#1)
      let elements : Int := (fdiv_int 64 esize)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMOVN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVN_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VMOVN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVN_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VMOV_h_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:28889.29-28889.30"
      if ((! (HaveFP16Ext ())) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((cond != 0b1110#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let to_arm_register : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_h_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) to_arm_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_h_T1enc_A_txt (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((! (HaveFP16Ext ())) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let to_arm_register : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_h_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) to_arm_register))
  else (pure (()))


end ArmFull.Functions
