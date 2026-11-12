import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0063
import ArmFull.Fn.M0124
import ArmFull.Fn.M0175
import ArmFull.Fn.M1176

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

def decode_aarch32_instrs_LDRD_l_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4491.29-4491.30"
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      if ((t2 == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRD_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))
        (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_LDRD_l_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := (U == 1#1)
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((W == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRD_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))
        (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_LDRD_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4586.29-4586.30"
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((((t2 == 15) || (m == 15)) || (m == t)) || (m == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && (((n == 15) || (n == t)) || (n == t2))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRD_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDREX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4641.29-4641.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Zeros (n := 32))
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREX_Op_A_txt imm32 (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDREX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREX_Op_A_txt imm32 (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDREXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4706.29-4706.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREXB_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDREXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREXB_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDREXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4772.29-4772.30"
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) || (t2 == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREXD_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_LDREXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let n : Int := (BitVec.toNat Rn)
      if (((((t == 15) || (t2 == 15)) || (t == t2)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREXD_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_LDREXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4837.29-4837.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREXH_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDREXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDREXH_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRH_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4907.29-4907.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRH (literal)"))
      else (pure (()))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRHT"))
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
      (execute_aarch32_instrs_LDRH_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRH_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm5 +++ 0#1) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRH_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRH_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD (immediate)"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRH (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRH_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRH_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRH (literal)"))
      else (pure (()))
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "PLDW (immediate)"))
      else (pure (()))
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "LDRHT"))
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
      (execute_aarch32_instrs_LDRH_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRH_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5069.29-5069.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRHT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRH_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRH_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRH_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRH_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5143.29-5143.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3046) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3047) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRHT"))
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
      (execute_aarch32_instrs_LDRH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRH_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3048) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3049) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_LDRH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRH_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3050) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3051) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRH (literal)"))
      else (pure (()))
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLDW (register)"))
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
      (execute_aarch32_instrs_LDRH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRHT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5274.29-5274.30"
      let m ← (( do (undefined_int_at (← occLabel 3052) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3053) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3054) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_LDRHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRHT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5310.29-5310.30"
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3055) 32) ) : SailM (BitVec 32) )
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
      (execute_aarch32_instrs_LDRHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRHT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3056) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3057) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3058) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRH (literal)"))
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
      (execute_aarch32_instrs_LDRHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDR_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:5406.29-5406.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDR (literal)"))
      else (pure (()))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((wback && (n == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDR_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm5 +++ 0b00#2) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDR_i_T2enc_A_txt (Rt : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Nat := 13
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index n (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDR_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDR (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
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
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDR_i_T4enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDR (literal)"))
      else (pure (()))
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "LDRT"))
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
      let w__5 ← (( do
        if ((wback && (n == t)) : Bool)
        then (pure true)
        else
          (do
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
            else (pure false)) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


end ArmFull.Functions
