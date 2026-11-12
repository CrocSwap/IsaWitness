import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0063
import ArmFull.Fn.M0124
import ArmFull.Fn.M0175
import ArmFull.Fn.M1176
import ArmFull.Fn.M1177

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

def decode_aarch32_instrs_LDR_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5602.29-5602.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (wback : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDR_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDR_l_T1enc_A_txt (Rt : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := true
      (execute_aarch32_instrs_LDR_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDR_l_T2enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let w__4 ← (( do
        if ((← do
             if (((t == 15) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDR_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDR_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5702.29-5702.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3059) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3060) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDR_r_OpA_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3061) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3062) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LDR_r_OpT_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDR_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3063) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3064) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDR (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             if (((t == 15) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDR_r_OpT_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5844.29-5844.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSB (literal)"))
      else (pure (()))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRSBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSB_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_i_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLI"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSB (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRSB_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "PLI"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSB (literal)"))
      else (pure (()))
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "LDRSBT"))
      else (pure (()))
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSB_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5964.29-5964.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRSBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSB_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLI"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRSB_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:6038.29-6038.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3065) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3066) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRSBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3067) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3068) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LDRSB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSB_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3069) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3070) ()) ) : SailM SRType )
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLI"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSB (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSBT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:6169.29-6169.30"
      let m ← (( do (undefined_int_at (← occLabel 3071) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3072) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3073) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      (execute_aarch32_instrs_LDRSBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSBT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:6205.29-6205.30"
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3074) 32) ) : SailM (BitVec 32) )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      (execute_aarch32_instrs_LDRSBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSBT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3075) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3076) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3077) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSB (literal)"))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:6293.29-6293.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSH (literal)"))
      else (pure (()))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRSHT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSH_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_i_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSH (literal)"))
      else (pure (()))
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "Related instructions"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRSH_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSH (literal)"))
      else (pure (()))
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related instructions"))
      else (pure (()))
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "LDRSHT"))
      else (pure (()))
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSH_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:6414.29-6414.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRSHT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSH_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "Related instructions"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRSH_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:6488.29-6488.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3078) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3079) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRSHT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3080) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3081) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LDRSH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRSH_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3082) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3083) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSH (literal)"))
      else (pure (()))
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "Related instructions"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


end ArmFull.Functions
