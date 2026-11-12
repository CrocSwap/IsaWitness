import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0124
import ArmFull.Fn.M0225
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

def decode_aarch32_instrs_UHSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UHSAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UHSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:17658.29-17658.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UHSUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UHSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UHSUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UHSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:17725.29-17725.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UHSUB8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UHSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UHSUB8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UMAAL_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:17787.29-17787.30"
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UMAAL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UMAAL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UMAAL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UMLAL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:17860.29-17860.30"
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UMLAL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        setflags))
  else (pure (()))


def decode_aarch32_instrs_UMLAL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := false
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UMLAL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        setflags))
  else (pure (()))


def decode_aarch32_instrs_UMULL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:17936.29-17936.30"
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UMULL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        setflags))
  else (pure (()))


def decode_aarch32_instrs_UMULL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := false
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UMULL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        setflags))
  else (pure (()))


def decode_aarch32_instrs_UQADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18008.29-18008.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UQADD16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UQADD16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18075.29-18075.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UQADD8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UQADD8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18138.29-18138.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UQASX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UQASX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18201.29-18201.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UQSAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UQSAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18264.29-18264.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UQSUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UQSUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18331.29-18331.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_UQSUB8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_UQSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_UQSUB8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USAD8_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18396.29-18396.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USAD8_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USAD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_USAD8_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USADA8_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18457.29-18457.30"
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "USAD8"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USADA8_Op_A_txt (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USADA8_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "USAD8"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USADA8_Op_A_txt (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USAT16_A1enc_A_txt (cond : (BitVec 4)) (sat_imm : (BitVec 4)) (Rd : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18534.29-18534.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let saturate_to : Int := (BitVec.toNat sat_imm)
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USAT16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (saturate_to))))
  else (pure (()))


def decode_aarch32_instrs_USAT16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (sat_imm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let saturate_to : Int := (BitVec.toNat sat_imm)
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USAT16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (saturate_to))))
  else (pure (()))


def decode_aarch32_instrs_USAT_A1enc_A_txt (cond : (BitVec 4)) (sat_imm : (BitVec 5)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (sh : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18606.29-18606.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3330) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3331) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let saturate_to : Int := (BitVec.toNat sat_imm)
      let w__1 ← (( do (DecodeImmShift (sh +++ 0#1) imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_USAT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (saturate_to)) shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_USAT_T1enc_A_txt (sh : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (sat_imm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3332) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3333) ()) ) : SailM SRType )
      if (((sh == 1#1) && ((imm3 +++ imm2) == 0b00000#5)) : Bool)
      then sailThrow ((Error_See "USAT16"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let saturate_to : Int := (BitVec.toNat sat_imm)
      let w__1 ← (( do (DecodeImmShift (sh +++ 0#1) (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USAT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (saturate_to)) shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_USAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18689.29-18689.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_USAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:18754.29-18754.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_USUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_USUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_USUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


end ArmFull.Functions
