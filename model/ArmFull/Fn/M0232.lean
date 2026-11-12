import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0124
import ArmFull.Fn.M0220
import ArmFull.Fn.M0223
import ArmFull.Fn.M0224

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

def decode_aarch32_instrs_SBFX_A1enc_A_txt (cond : (BitVec 4)) (widthm1 : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11119.29-11119.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let lsbit : Int := (BitVec.toNat lsb)
      let widthminus1 : Int := (BitVec.toNat widthm1)
      let msbit : Int := (lsbit +i widthminus1)
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((msbit >b 31) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SBFX_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (lsbit)) msbit (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SBFX_T1enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (widthm1 : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let lsbit : Int := (BitVec.toNat (imm3 +++ imm2))
      let widthminus1 : Int := (BitVec.toNat widthm1)
      let msbit : Int := (lsbit +i widthminus1)
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((msbit >b 31) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SBFX_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (lsbit)) msbit (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SDIV_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11199.29-11199.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a != 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SDIV_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SDIV_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a != 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SDIV_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SEL_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11274.29-11274.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SEL_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SEL_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SEL_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


/-- Type quantifiers: k_set_bigend : Bool -/
def execute_aarch32_instrs_SETEND_Op_A_txt (set_bigend : Bool) : SailM Unit := do
  (AArch32_CheckSETENDEnabled ())
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with E := if (set_bigend : Bool)
    then 1#1
    else 0#1 }


def decode_aarch32_instrs_SHADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11440.29-11440.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SHADD16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SHADD16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11507.29-11507.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SHADD8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SHADD8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11570.29-11570.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SHASX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SHASX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11633.29-11633.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SHSAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SHSAX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11696.29-11696.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SHSUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SHSUB16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11763.29-11763.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SHSUB8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SHSUB8_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLABB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (N : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11832.29-11832.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLABB_Op_A_txt (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) m_high (Sail.Int.toNatChecked (n))
        n_high))
  else (pure (()))


def decode_aarch32_instrs_SMLABB_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SMULBB, SMULBT, SMULTB, SMULTT"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLABB_Op_A_txt (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) m_high (Sail.Int.toNatChecked (n))
        n_high))
  else (pure (()))


def decode_aarch32_instrs_SMLAD_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11911.29-11911.30"
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SMUAD"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLAD_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLAD_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SMUAD"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLAD_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLAL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:11988.29-11988.30"
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
      (execute_aarch32_instrs_SMLAL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        setflags))
  else (pure (()))


def decode_aarch32_instrs_SMLAL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_SMLAL_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        setflags))
  else (pure (()))


def decode_aarch32_instrs_SMLALBB_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (N : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:12063.29-12063.30"
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLALBB_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) m_high (Sail.Int.toNatChecked (n))
        n_high))
  else (pure (()))


def decode_aarch32_instrs_SMLALBB_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLALBB_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) m_high (Sail.Int.toNatChecked (n))
        n_high))
  else (pure (()))


def decode_aarch32_instrs_SMLALD_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:12142.29-12142.30"
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLALD_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLALD_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLALD_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLAWB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:12219.29-12219.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let m_high : Bool := (M == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLAWB_Op_A_txt (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) m_high (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLAWB_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SMULWB, SMULWT"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLAWB_Op_A_txt (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) m_high (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLSD_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:12294.29-12294.30"
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SMUSD"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLSD_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLSD_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SMUSD"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLSD_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SMLSLD_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:12369.29-12369.30"
      let dLo : Int := (BitVec.toNat RdLo)
      let dHi : Int := (BitVec.toNat RdHi)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((dHi == dLo) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMLSLD_Op_A_txt (Sail.Int.toNatChecked (dHi))
        (Sail.Int.toNatChecked (dLo)) (Sail.Int.toNatChecked (m)) m_swap (Sail.Int.toNatChecked (n))))
  else (pure (()))


end ArmFull.Functions
