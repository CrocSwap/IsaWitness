import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044

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

def _set_SCTLR_EL3_Type_TCF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_TCF r v)


def _set_SCTLR_EL2_Type_TCF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCF0 r v)


def _set_SCTLR_EL1_Type_TCF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCF0 r v)


def _set_SCTLR_EL2_Type_TCSO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCSO r v)


def _set_SCTLR_EL1_Type_TCSO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCSO r v)


def _set_SCTLR_EL3_Type_TCSO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_TCSO r v)


def _set_SCTLR_EL2_Type_TCSO0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCSO0 r v)


def _set_SCTLR_EL1_Type_TCSO0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCSO0 r v)


def _set_SCTLR_EL1_Type_BT1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_BT1 r v)


def _set_SCTLR_Type_AFE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_AFE r v)


def _set_SCTLR_Type_TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_TRE r v)


def _set_SCTLR_Type_UNK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_UNK r v)


def _set_SCTLR_Type_UWXN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_UWXN r v)


def SCTLR_read (regime : (BitVec 2)) : SailM (BitVec 64) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 667) 64) ) : SailM (BitVec 64) )
  let questionMark := regime
  let r ← (( do
    if ((questionMark == EL1) : Bool)
    then
      (do
        readReg SCTLR_EL1)
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            readReg SCTLR_EL2)
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                readReg SCTLR_EL3)
            else
              (do
                (Unreachable ())
                (pure (r))))) ) : SailM (BitVec 64) )
  (pure ((Mk_SCTLRType r)))


def _set_ESR_EL1_Type_ISS2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESR_EL1_Type_ISS2 r v)


def _set_ESR_EL2_Type_ISS2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESR_EL2_Type_ISS2 r v)


def _set_ESR_EL3_Type_ISS2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESR_EL3_Type_ISS2 r v)


def ESR_set (regime : (BitVec 2)) (value_name : (BitVec 64)) : SailM Unit := do
  let r : (BitVec 64) := value_name
  let questionMark := regime
  if ((questionMark == EL1) : Bool)
  then
    (do
      writeReg ESR_EL1 (Mk_ESR_EL1_Type r))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          writeReg ESR_EL2 (Mk_ESR_EL2_Type r))
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              writeReg ESR_EL3 (Mk_ESR_EL3_Type r))
          else
            (do
              (Unreachable ()))))


def FAR_set (regime : (BitVec 2)) (value_name : (BitVec 64)) : SailM Unit := do
  let r : (BitVec 64) := value_name
  let questionMark := regime
  if ((questionMark == EL1) : Bool)
  then
    (do
      writeReg FAR_EL1 r)
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          writeReg FAR_EL2 r)
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              writeReg FAR_EL3 r)
          else
            (do
              (Unreachable ()))))


def _set_HPFAR_EL2_Type_FIPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HPFAR_EL2_Type_FIPA r v)


def _set_HPFAR_Type_FIPA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 28)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HPFAR_Type_FIPA r v)


def _set_MFAR_EL3_Type_FPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MFAR_EL3_Type_FPA r v)


def ELR_set (el : (BitVec 2)) (value_name : (BitVec 64)) : SailM Unit := do
  let r : (BitVec 64) := value_name
  let questionMark := el
  if ((questionMark == EL1) : Bool)
  then
    (do
      writeReg ELR_EL1 r)
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          writeReg ELR_EL2 r)
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              writeReg ELR_EL3 r)
          else
            (do
              (Unreachable ()))))


def ResetSVEState (_ : Unit) : SailM Unit := do
  let loop_n_lower : Nat := 0
  let loop_n_upper : Nat := 31
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
        writeReg _Z (vectorUpdate w__0 (Sail.Int.toNatChecked (n))
          (Sail.BitVec.castWidth (m := 2048) (Zeros (n := MAX_VL))))
    (pure loop_vars))
  let loop_n_lower : Nat := 0
  let loop_n_upper : Nat := 15
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__1 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
        writeReg _P (vectorUpdate w__1 (Sail.Int.toNatChecked (n))
          (Sail.BitVec.castWidth (m := 256) (Zeros (n := MAX_PL))))
    (pure loop_vars))
  writeReg _FFR (Sail.BitVec.castWidth (m := 256) (Zeros (n := MAX_PL)))
  writeReg FPSR (Mk_FPSR_Type (Sail.BitVec.zeroExtend 0x0800009F#32 64))


def _set_SPSR_abt_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_abt_Type_J r v)


def _set_SPSR_fiq_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_fiq_Type_J r v)


def _set_SPSR_hyp_Type_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_hyp_Type_J r v)


def _set_SPSR_irq_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_J r v)


def _set_SPSR_mon_Type_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_J r v)


def _set_SPSR_svc_Type_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_J r v)


def _set_SPSR_und_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_J r v)


def _set_EDECCR_Type_NSE0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSE0 r v)


def _set_EDECCR_Type_NSE1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSE1 r v)


def _set_EDECCR_Type_NSE2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSE2 r v)


def _set_EDECCR_Type_NSE3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSE3 r v)


def _set_EDECCR_Type_NSR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSR0 r v)


def _set_EDECCR_Type_NSR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSR1 r v)


def _set_EDECCR_Type_NSR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSR2 r v)


def _set_EDECCR_Type_NSR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_NSR3 r v)


def _set_EDECCR_Type_RLE0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_RLE0 r v)


def _set_EDECCR_Type_RLE1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_RLE1 r v)


def _set_EDECCR_Type_RLE2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_RLE2 r v)


def _set_EDECCR_Type_RLR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_RLR0 r v)


def _set_EDECCR_Type_RLR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_RLR1 r v)


def _set_EDECCR_Type_RLR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_RLR2 r v)


def _set_EDECCR_Type_SE0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SE0 r v)


def _set_EDECCR_Type_SE1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SE1 r v)


def _set_EDECCR_Type_SE2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SE2 r v)


def _set_EDECCR_Type_SE3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SE3 r v)


def _set_EDECCR_Type_SR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SR0 r v)


def _set_EDECCR_Type_SR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SR1 r v)


def _set_EDECCR_Type_SR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SR2 r v)


def _set_EDECCR_Type_SR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDECCR_Type_SR3 r v)


def _set_OSECCR_EL1_Type_EDECCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_OSECCR_EL1_Type_EDECCR r v)


def _set_DBGOSECCR_Type_EDECCR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGOSECCR_Type_EDECCR r v)


def _set_EDESR_Type_OSUC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDESR_Type_OSUC r v)


def _set_EDESR_Type_RC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDESR_Type_RC r v)


def VBAR_read (regime : (BitVec 2)) : SailM (BitVec 64) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 706) 64) ) : SailM (BitVec 64) )
  let questionMark := regime
  if ((questionMark == EL1) : Bool)
  then
    (do
      readReg VBAR_EL1)
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          readReg VBAR_EL2)
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              readReg VBAR_EL3)
          else
            (do
              (Unreachable ())
              (pure (r)))))


def __GIC_InterruptPending (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg __GIC_Pending ) : SailM (Option InterruptID) )
  (pure ((is_some w__0)))


/-- Type quantifiers: localtimeout : Int -/
def LocalTimeoutEvent (localtimeout : Int) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: delay : Int, k_delay_enabled : Bool -/
def WaitForEventUntilDelay (delay_enabled : Bool) (delay : Int) : SailM Bool := do
  (__UNKNOWN_boolean ())


def VirtualFIQPending (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def VirtualIRQPending (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def _set_GCSCRE0_EL1_Type_nTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_nTR r v)


def GCSPCRSelected (el : (BitVec 2)) : SailM Bool := SailME.run do
  let questionMark := el
  if ((questionMark == EL0) : Bool)
  then
    (do
      let w__0 ← (( do readReg GCSCRE0_EL1 ) : SailME Bool (BitVec 64) )
      SailME.throw (((_get_GCSCRE0_EL1_Type_PCRSEL w__0) == 1#1) : Bool))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__1 ← (( do readReg GCSCR_EL1 ) : SailME Bool (BitVec 64) )
          SailME.throw (((_get_GCSCR_EL1_Type_PCRSEL w__1) == 1#1) : Bool))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__2 ← (( do readReg GCSCR_EL2 ) : SailME Bool (BitVec 64) )
              SailME.throw (((_get_GCSCR_EL2_Type_PCRSEL w__2) == 1#1) : Bool))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do readReg GCSCR_EL3 ) : SailME Bool (BitVec 64) )
                  SailME.throw (((_get_GCSCR_EL3_Type_PCRSEL w__3) == 1#1) : Bool))
              else (pure (())))))
  (Unreachable ())
  (pure (true))


def _set_HCRX_EL2_Type_EnSDERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnSDERR r v)


def _set_HCRX_EL2_Type_EnSNERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnSNERR r v)


def _set_HCRX_EL2_Type_FGTnXS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_FGTnXS r v)


def _set_HCRX_EL2_Type_FnXS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_FnXS r v)


def _set_HCRX_EL2_Type_MCE2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_MCE2 r v)


def _set_HCRX_EL2_Type_SMPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_SMPME r v)


def _set_HCRX_EL2_Type_TALLINT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_TALLINT r v)


def _set_HCRX_EL2_Type_VFNMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_VFNMI r v)


def _set_HCRX_EL2_Type_VINMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_VINMI r v)


def _set_MPAM2_EL2_Type_ALTSP_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_ALTSP_EL2 r v)


def _set_MPAM2_EL2_Type_ALTSP_FRCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_ALTSP_FRCD r v)


def _set_MPAM1_EL1_Type_ALTSP_FRCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_ALTSP_FRCD r v)


def _set_MPAM2_EL2_Type_ALTSP_HFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_ALTSP_HFC r v)


def _set_MPAM3_EL3_Type_ALTSP_HFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_ALTSP_HFC r v)


def _set_MPAM2_EL2_Type_EnMPAMSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_EnMPAMSM r v)


def _set_MPAM2_EL2_Type_MPAMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_MPAMEN r v)


def _set_MPAM1_EL1_Type_MPAMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_MPAMEN r v)


def _set_MPAM3_EL3_Type_MPAMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_MPAMEN r v)


def _set_MPAM2_EL2_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PARTID_D r v)


def _set_MPAM0_EL1_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PARTID_D r v)


def _set_MPAM1_EL1_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PARTID_D r v)


def _set_MPAM3_EL3_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PARTID_D r v)


def _set_MPAMSM_EL1_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMSM_EL1_Type_PARTID_D r v)


def _set_MPAM2_EL2_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PARTID_I r v)


def _set_MPAM0_EL1_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PARTID_I r v)


def _set_MPAM1_EL1_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PARTID_I r v)


def _set_MPAM3_EL3_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PARTID_I r v)


def _set_MPAM2_EL2_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PMG_D r v)


def _set_MPAM0_EL1_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PMG_D r v)


def _set_MPAM1_EL1_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PMG_D r v)


def _set_MPAM3_EL3_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PMG_D r v)


def _set_MPAMSM_EL1_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMSM_EL1_Type_PMG_D r v)


def _set_MPAM2_EL2_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PMG_I r v)


def _set_MPAM0_EL1_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PMG_I r v)


def _set_MPAM1_EL1_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PMG_I r v)


def _set_MPAM3_EL3_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PMG_I r v)


def _set_MPAM2_EL2_Type_TIDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_TIDR r v)


def _set_MPAM2_EL2_Type_TRAPMPAM0EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_TRAPMPAM0EL1 r v)


def _set_MPAM2_EL2_Type_TRAPMPAM1EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM2_EL2_Type_TRAPMPAM1EL1 r v)


def _set_MPAM3_EL3_Type_ALTSP_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_ALTSP_EL3 r v)


def _set_MPAM3_EL3_Type_ALTSP_HEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_ALTSP_HEN r v)


def _set_MPAM3_EL3_Type_FORCE_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_FORCE_NS r v)


def _set_MPAM3_EL3_Type_RT_ALTSP_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_RT_ALTSP_NS r v)


def _set_MPAM3_EL3_Type_SDEFLT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_SDEFLT r v)


def _set_MPAM3_EL3_Type_TRAPLOWER (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM3_EL3_Type_TRAPLOWER r v)


def MPAM3_EL3_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _MPAM3_EL3 ) : SailM MPAM3_EL3_Type )
  let w__0 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  let r := ((BitVec.update r 63 (Bit (BitVec.slice w__0 63 1))) : (BitVec 64))
  (pure (r))


def _set_MPAM1_EL1_Type_FORCED_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAM1_EL1_Type_FORCED_NS r v)


def _set_MPAMIDR_EL1_Type_HAS_ALTSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_ALTSP r v)


end ArmFull.Functions
