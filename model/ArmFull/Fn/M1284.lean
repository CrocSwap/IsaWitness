import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0124
import ArmFull.Fn.M1178

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

def decode_aarch32_instrs_STRD_i_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((wback && ((n == t) || (n == t2))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((n == 15) || (t == 15)) || (t2 == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRD_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRD_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14271.29-14271.30"
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
      if (((t2 == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && (((n == 15) || (n == t)) || (n == t2))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRD_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) wback))
  else (pure (()))


def decode_aarch32_instrs_STREX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14330.29-14330.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Zeros (n := 32))
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREX_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STREX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREX_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STREXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14405.29-14405.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREXB_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STREXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREXB_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STREXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14485.29-14485.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      if (((((d == 15) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1)) || (t2 == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((d == n) || (d == t)) || (d == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREXD_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_STREXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let n : Int := (BitVec.toNat Rn)
      if (((((d == 15) || (t == 15)) || (t2 == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((d == n) || (d == t)) || (d == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREXD_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_STREXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14560.29-14560.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREXH_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STREXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STREXH_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STRH_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14640.29-14640.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "STRHT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRH_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRH_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
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
      (execute_aarch32_instrs_STRH_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRH_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRH_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRH_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "STRHT"))
      else (pure (()))
      if (((Rn == 0b1111#4) || ((P == 0#1) && (W == 0#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRH_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRH_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14802.29-14802.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3246) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3247) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "STRHT"))
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
      (execute_aarch32_instrs_STRH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRH_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3248) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3249) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_STRH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRH_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3250) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3251) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
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
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRH_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRHT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14930.29-14930.30"
      let m ← (( do (undefined_int_at (← occLabel 3252) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3253) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3254) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_STRHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STRHT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:14966.29-14966.30"
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3255) 32) ) : SailM (BitVec 32) )
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
      (execute_aarch32_instrs_STRHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STRHT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3256) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3257) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3258) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
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
      (execute_aarch32_instrs_STRHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STR_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:15054.29-15054.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "STRT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STR_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
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
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_i_T2enc_A_txt (Rt : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
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
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index n (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_i_T4enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "STRT"))
      else (pure (()))
      if (((Rn == 0b1111#4) || ((P == 0#1) && (W == 0#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:15240.29-15240.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3260) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3261) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "STRT"))
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
      (execute_aarch32_instrs_STR_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3262) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3263) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_STR_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STR_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3264) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3265) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
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
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STR_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


end ArmFull.Functions
