import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0016
import ArmFull.Fn.M0024
import ArmFull.Fn.M0040
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0111
import ArmFull.Fn.M0112
import ArmFull.Fn.M0115
import ArmFull.Fn.M0118
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0151
import ArmFull.Fn.M0175
import ArmFull.Fn.M0181
import ArmFull.Fn.M0194
import ArmFull.Fn.M0202
import ArmFull.Fn.M0204
import ArmFull.Fn.M0218
import ArmFull.Fn.M0226

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

def decode_aarch32_instrs_USUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18825.29-18825.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USUB8_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USUB8_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UXTAB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18887.29-18887.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "UXTB16"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTAB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTAB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "UXTB16"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTAB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTAB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18962.29-18962.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "UXTB"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTAB_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTAB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "UXTB"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTAB_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTAH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:19037.29-19037.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "UXTH"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTAH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTAH_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "UXTH"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTAH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTB16_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:19113.29-19113.30"
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTB16_T1enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:19178.29-19178.30"
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTB_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTB_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Nat := 0
      (execute_aarch32_instrs_UXTB_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        rotation))
  else (pure (()))


def decode_aarch32_instrs_UXTB_T2enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTB_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTH_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:19262.29-19262.30"
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_UXTH_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Nat := 0
      (execute_aarch32_instrs_UXTH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        rotation))
  else (pure (()))


def decode_aarch32_instrs_UXTH_T2enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let rotation : Int := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UXTH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (rotation))))
  else (pure (()))


def decode_aarch32_instrs_MRS_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:41109.29-41109.30"
      let d : Int := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MRS_Op_AS_txt (Sail.Int.toNatChecked (d)) read_spsr))
  else (pure (()))


def decode_aarch32_instrs_MRS_T1enc_AS_txt (R : (BitVec 1)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MRS_Op_AS_txt (Sail.Int.toNatChecked (d)) read_spsr))
  else (pure (()))


def decode_aarch32_instrs_MSR_r_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (mask : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:41510.29-41510.30"
      let n : Int := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((mask == 0b0000#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MSR_r_Op_AS_txt mask (Sail.Int.toNatChecked (n)) write_spsr))
  else (pure (()))


def decode_aarch32_instrs_MSR_r_T1enc_AS_txt (R : (BitVec 1)) (Rn : (BitVec 4)) (mask : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((mask == 0b0000#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MSR_r_Op_AS_txt mask (Sail.Int.toNatChecked (n)) write_spsr))
  else (pure (()))


def decode_aarch32_instrs_CRC32_A1enc_A_txt (cond : (BitVec 4)) (sz : (BitVec 2)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (C : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:42477.29-42477.30"
      let w__1 ← (( do (HaveCRCExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let size : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let crc32c : Bool := (C == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((size == 64) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((cond != 0b1110#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CRC32_Op_A_txt crc32c (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (size))))
  else (pure (()))


def decode_aarch32_instrs_CRC32_T1enc_A_txt (C : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (sz : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveCRCExt ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let size : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let crc32c : Bool := (C == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((size == 64) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CRC32_Op_A_txt crc32c (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (size))))
  else (pure (()))


/-- Type quantifiers: k_ADD : Bool, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcaddtag (ADD : Bool) (d : Nat) (n : Nat) (offset : (BitVec 64)) (tag_offset : (BitVec 4)) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let start_tag : (BitVec 4) := (AArch64_AllocationTagFromAddress operand1)
  let w__2 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
  let exclude : (BitVec 16) := (_get_GCR_EL1_Type_Exclude w__2)
  let result ← (( do (undefined_bitvector_at (← occLabel 3931) 64) ) : SailM (BitVec 64) )
  let rtag ← (( do (undefined_bitvector_at (← occLabel 3932) 4) ) : SailM (BitVec 4) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__4 ← (( do (AArch64_AllocationTagAccessIsEnabled w__3.EL) ) : SailM Bool )
  let rtag ← (( do
    if (w__4 : Bool)
    then
      (do
        (AArch64_ChooseNonExcludedTag start_tag tag_offset exclude))
    else (pure (0b0000#4)) ) : SailM (BitVec 4) )
  let result : (BitVec 64) :=
    if (ADD : Bool)
    then
      (let (__tup_0, _) := (AddWithCarry operand1 offset 0#1)
      __tup_0)
    else
      (let (__tup_0, _) := (AddWithCarry operand1 (Complement.complement offset) 1#1)
      __tup_0)
  let result ← (( do (AArch64_AddressWithAllocationTag result rtag) ) : SailM (BitVec 64) )
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcinsertrandomtag (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let exclude_reg ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let w__2 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
  let exclude : (BitVec 16) :=
    ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb exclude_reg 15 0)) ||| (_get_GCR_EL1_Type_Exclude
        w__2))
  let rtag ← (( do (undefined_bitvector_at (← occLabel 4334) 4) ) : SailM (BitVec 4) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__4 ← (( do (AArch64_AllocationTagAccessIsEnabled w__3.EL) ) : SailM Bool )
  let rtag ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
        if (((_get_GCR_EL1_Type_RRND w__5) == 1#1) : Bool)
        then
          (do
            if ((IsOnes exclude) : Bool)
            then (pure (0b0000#4))
            else
              (do
                (ChooseRandomNonExcludedTag exclude)))
        else
          (do
            let w__7 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
            let start_tag : (BitVec 4) := (_get_RGSR_EL1_Type_TAG w__7)
            let offset ← (( do (AArch64_RandomTag ()) ) : SailM (BitVec 4) )
            let w__8 ← (( do (AArch64_ChooseNonExcludedTag start_tag offset exclude) ) : SailM
              (BitVec 4) )
            let rtag := (w__8 : (BitVec 4))
            let w__9 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
            writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__9 3 0 rtag)
            (pure (rtag))))
    else (pure (0b0000#4)) ) : SailM (BitVec 4) )
  let result ← (( do (AArch64_AddressWithAllocationTag operand rtag) ) : SailM (BitVec 64) )
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: k_ADD : Bool, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsubtag (ADD : Bool) (d : Nat) (n : Nat) (offset : (BitVec 64)) (tag_offset : (BitVec 4)) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let start_tag : (BitVec 4) := (AArch64_AllocationTagFromAddress operand1)
  let w__2 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
  let exclude : (BitVec 16) := (_get_GCR_EL1_Type_Exclude w__2)
  let result ← (( do (undefined_bitvector_at (← occLabel 5006) 64) ) : SailM (BitVec 64) )
  let rtag ← (( do (undefined_bitvector_at (← occLabel 5007) 4) ) : SailM (BitVec 4) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__4 ← (( do (AArch64_AllocationTagAccessIsEnabled w__3.EL) ) : SailM Bool )
  let rtag ← (( do
    if (w__4 : Bool)
    then
      (do
        (AArch64_ChooseNonExcludedTag start_tag tag_offset exclude))
    else (pure (0b0000#4)) ) : SailM (BitVec 4) )
  let result : (BitVec 64) :=
    if (ADD : Bool)
    then
      (let (__tup_0, _) := (AddWithCarry operand1 offset 0#1)
      __tup_0)
    else
      (let (__tup_0, _) := (AddWithCarry operand1 (Complement.complement offset) 1#1)
      __tup_0)
  let result ← (( do (AArch64_AddressWithAllocationTag result rtag) ) : SailM (BitVec 64) )
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: k_cond : Bool -/
def BRBEBranch (br_type : BranchType) (cond : Bool) (target_address : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let branch_valid ← (( do (BranchRecordAllowed w__0.EL) ) : SailM Bool )
  let w__2 ← (( do
    if (branch_valid : Bool)
    then
      (do
        (FilterBranchRecord br_type cond))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let branch_type ← (( do (undefined_bitvector_at (← occLabel 575) 6) ) : SailM (BitVec 6) )
      let branch_type ← (( do
        match br_type with
        | .BranchType_DIR =>
          (let branch_type : (BitVec 6) :=
            if (cond : Bool)
            then 0b001000#6
            else 0b000000#6
          (pure (branch_type)))
        | .BranchType_INDIR => (pure (0b000001#6))
        | .BranchType_DIRCALL => (pure (0b000010#6))
        | .BranchType_INDCALL => (pure (0b000011#6))
        | .BranchType_RET => (pure (0b000101#6))
        | _ =>
          (do
            (Unreachable ())
            (pure (branch_type))) ) : SailM (BitVec 6) )
      let ccu ← (( do (undefined_bitvector_at (← occLabel 576) 1) ) : SailM (BitVec 1) )
      let cc ← (( do (undefined_bitvector_at (← occLabel 577) 14) ) : SailM (BitVec 14) )
      let w__3 ← (( do (BranchEncCycleCount ()) ) : SailM ((BitVec 1) × (BitVec 14)) )
      let (tup__0, tup__1) := (w__3 : ((BitVec 1) × (BitVec 14)))
      let ccu : (BitVec 1) := tup__0
      let cc : (BitVec 14) := tup__1
      let w__4 ← (( do (HaveTME ()) ) : SailM Bool )
      let lastfailed ← (( do
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
            (pure ((_get_BRBFCR_EL1_Type_LASTFAILED w__5))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let w__8 ← (( do
        if ((← do
             (HaveTME ())) : Bool)
        then
          (do
            let w__7 ← (( do readReg TSTATE ) : SailM TMState )
            (pure (((w__7.depth >b 0) : Bool))))
        else (pure false) ) : SailM Bool )
      let transactional : (BitVec 1) :=
        if (w__8 : Bool)
        then 1#1
        else 0#1
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      let el : (BitVec 2) := w__9.EL
      let w__11 ← (( do
        (pure ((← do
              (BRBEMispredictAllowed ())) && ((BranchMispredict ()) : Bool))) ) : SailM Bool )
      let mispredict : (BitVec 1) :=
        if (w__11 : Bool)
        then 1#1
        else 0#1
      let w__12 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (UpdateBranchRecordBuffer ccu cc lastfailed transactional branch_type el mispredict 0b11#2
        w__12 target_address)
      let w__13 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__13 6 6 0#1)
      (PMUEvent PMU_EVENT_BRB_FILTRATE))
  else (pure (()))
  writeReg __last_branch_valid branch_valid


def RestoreTransactionCheckpoint (_ : Unit) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let VL : Int := VL
  match VL with
  | 128 =>
    (do
      (RestoreTransactionCheckpointParameterised (Sail.Int.toNatChecked (VL))
        (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (VL)) 8)))))
  | 256 =>
    (do
      (RestoreTransactionCheckpointParameterised (Sail.Int.toNatChecked (VL))
        (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (VL)) 8)))))
  | 512 =>
    (do
      (RestoreTransactionCheckpointParameterised (Sail.Int.toNatChecked (VL))
        (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (VL)) 8)))))
  | 1024 =>
    (do
      (RestoreTransactionCheckpointParameterised (Sail.Int.toNatChecked (VL))
        (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (VL)) 8)))))
  | 2048 =>
    (do
      (RestoreTransactionCheckpointParameterised (Sail.Int.toNatChecked (VL))
        (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (VL)) 8)))))
  | _ =>
    (do
      ArmFull.assert false "sail-arm/v8_base.sail:7561.22-7561.23"
      throw Error.Exit)


end ArmFull.Functions
