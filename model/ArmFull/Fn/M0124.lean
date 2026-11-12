import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0062
import ArmFull.Fn.M0063

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

def _set_DACR32_EL2_Type_D14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D14 r v)


def _set_DACR_Type_D14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D14 r v)


def _set_DACR32_EL2_Type_D15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D15 r v)


def _set_DACR_Type_D15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D15 r v)


def _set_DACR32_EL2_Type_D2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D2 r v)


def _set_DACR_Type_D2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D2 r v)


def _set_DACR32_EL2_Type_D3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D3 r v)


def _set_DACR_Type_D3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D3 r v)


def _set_DACR32_EL2_Type_D4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D4 r v)


def _set_DACR_Type_D4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D4 r v)


def _set_DACR32_EL2_Type_D5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D5 r v)


def _set_DACR_Type_D5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D5 r v)


def _set_DACR32_EL2_Type_D6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D6 r v)


def _set_DACR_Type_D6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D6 r v)


def _set_DACR32_EL2_Type_D7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D7 r v)


def _set_DACR_Type_D7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D7 r v)


def _set_DACR32_EL2_Type_D8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D8 r v)


def _set_DACR_Type_D8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D8 r v)


def _set_DACR32_EL2_Type_D9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D9 r v)


def _set_DACR_Type_D9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D9 r v)


def RemapRegsHaveResetValues (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def _set_PAR_Type_ATTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_ATTR r v)


def _set_PAR_EL1_Type_ATTR (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_ATTR r v)


def _set_PAR_Type_FST (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_FST r v)


def _set_PAR_EL1_Type_FST (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_FST r v)


def _set_PAR_Type_FSTAGE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_FSTAGE r v)


def _set_PAR_Type_Inner (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_Inner r v)


def _set_PAR_Type_Outer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_Outer r v)


def _set_PAR_Type_S2WLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_S2WLK r v)


def _set_PAR_EL1_Type_TopLevel (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_TopLevel r v)


def __IMPDEF_bit (x : String) : SailM (BitVec 1) := do
  (__UNKNOWN_bit ())


def _set_CTILSR_Type_SLI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTILSR_Type_SLI r v)


def _set_EDLSR_Type_SLI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDLSR_Type_SLI r v)


def _set_PMLSR_Type_SLI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMLSR_Type_SLI r v)


def _set_CTILSR_Type_SLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTILSR_Type_SLK r v)


def _set_EDLSR_Type_SLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDLSR_Type_SLK r v)


def _set_PMLSR_Type_SLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMLSR_Type_SLK r v)


def _set_DBGDTR_EL0_Type_HighWord (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGDTR_EL0_Type_HighWord r v)


def _set_DBGDTR_EL0_Type_LowWord (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGDTR_EL0_Type_LowWord r v)


def _set_EDPRSR_Type_HALTED (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_HALTED r v)


def _set_EDPRSR_Type_PU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_PU r v)


def _set_EDPRSR_Type_R (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_R r v)


def _set_EDPRSR_Type_SDAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_SDAD r v)


def _set_EDPRSR_Type_SDR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_SDR r v)


def _set_EDPRSR_Type_SPMAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_SPMAD r v)


def _set_EDPRSR_Type_SR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_SR r v)


def _set_GICM_TYPER_Type_SR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_TYPER_Type_SR r v)


def _set_DBGDCCINT_Type_RX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDCCINT_Type_RX r v)


def _set_MDCCINT_EL1_Type_RX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCCINT_EL1_Type_RX r v)


def _set_DBGDCCINT_Type_TX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDCCINT_Type_TX r v)


def _set_MDCCINT_EL1_Type_TX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCCINT_EL1_Type_TX r v)


def _set_EDVIDSR_Type_CONTEXTIDR_EL2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDVIDSR_Type_CONTEXTIDR_EL2 r v)


def _set_EDVIDSR_Type_HV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDVIDSR_Type_HV r v)


def _set_PMPCSR_Type_PCSample (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMPCSR_Type_PCSample r v)


def _set_DBGDEVID_Type_PCSample (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_PCSample r v)


def _set_EDDEVID_Type_PCSample (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVID_Type_PCSample r v)


def _set_PMDEVID_Type_PCSample (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMDEVID_Type_PCSample r v)


def _set_HTRFCR_Type_E0HTRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HTRFCR_Type_E0HTRE r v)


def _set_TRFCR_EL2_Type_E0HTRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL2_Type_E0HTRE r v)


def _set_HTRFCR_Type_E2TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HTRFCR_Type_E2TRE r v)


def _set_TRFCR_EL2_Type_E2TRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL2_Type_E2TRE r v)


def _set_TRFCR_EL1_Type_E0TRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL1_Type_E0TRE r v)


def _set_TRFCR_Type_E0TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TRFCR_Type_E0TRE r v)


def _set_TRFCR_EL1_Type_E1TRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL1_Type_E1TRE r v)


def _set_TRFCR_Type_E1TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TRFCR_Type_E1TRE r v)


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV82 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap2_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV81 enabled))
  else (pure (()))


def _set_DBGVCR32_EL2_Type_NSD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSD r v)


def _set_DBGVCR_Type_NSD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_NSD r v)


def _set_DBGVCR32_EL2_Type_NSF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSF r v)


def _set_DBGVCR_Type_NSF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_NSF r v)


def _set_DBGVCR32_EL2_Type_NSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSI r v)


def _set_DBGVCR_Type_NSI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_NSI r v)


def _set_DBGVCR32_EL2_Type_NSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSP r v)


def _set_DBGVCR_Type_NSP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_NSP r v)


def _set_DBGVCR32_EL2_Type_NSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSS r v)


def _set_DBGVCR_Type_NSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_NSS r v)


def _set_DBGVCR32_EL2_Type_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SD r v)


def _set_DBGVCR_Type_SD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_SD r v)


def _set_DBGVCR32_EL2_Type_SF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SF r v)


def _set_DBGVCR_Type_SF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_SF r v)


def _set_DBGVCR32_EL2_Type_SI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SI r v)


def _set_DBGVCR_Type_SI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_SI r v)


def _set_DBGVCR32_EL2_Type_SP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SP r v)


def _set_DBGVCR_Type_SP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_SP r v)


def _set_DBGVCR32_EL2_Type_SU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SU r v)


def _set_DBGVCR_Type_SU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_SU r v)


def _set_DBGVCR_Type_MD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_MD r v)


def _set_DBGVCR_Type_MF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_MF r v)


def _set_DBGVCR_Type_MI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_MI r v)


def _set_DBGVCR_Type_MP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_MP r v)


def _set_DBGVCR_Type_MS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_MS r v)


def AArch32_PARInnerAttrs (memattrs : MemoryAttributes) : SailM (BitVec 3) := do
  let result ← (( do (undefined_bitvector_at (← occLabel 2686) 3) ) : SailM (BitVec 3) )
  let result : (BitVec 3) :=
    if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
    then
      (if ((BEq.beq memattrs.device DeviceType_nGnRnE) : Bool)
      then 0b001#3
      else
        (if ((BEq.beq memattrs.device DeviceType_nGnRE) : Bool)
        then 0b011#3
        else result))
    else
      (let inner : MemAttrHints := memattrs.inner
      if ((inner.attrs == MemAttr_NC) : Bool)
      then 0b000#3
      else
        (if (((inner.attrs == MemAttr_WB) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   inner.hints 0)])) == 1#1)) : Bool)
        then 0b101#3
        else
          (if ((inner.attrs == MemAttr_WT) : Bool)
          then 0b110#3
          else
            (if (((inner.attrs == MemAttr_WB) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       inner.hints 0)])) == 0#1)) : Bool)
            then 0b111#3
            else result))))
  (pure (result))


/-- Type quantifiers: k_N : Nat, k_N > 1 -/
def RRX_C (x : (BitVec k_N)) (carry_in : (BitVec 1)) : ((BitVec k_N) × (BitVec 1)) :=
  let result : (BitVec k_N) :=
    (BitVec.update (x >>> 1) (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i 1))) (Bit carry_in))
  let carry_out : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access x 0)]))
  (result, carry_out)


def DecodeImmShift (srtype : (BitVec 2)) (imm5 : (BitVec 5)) : SailM (SRType × Int) := do
  let shift_t ← (( do (undefined_SRType (← occLabel 2700) ()) ) : SailM SRType )
  let shift_n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 2701) 0 32))) ) :
    SailM Nat )
  let (shift_n, shift_t) : (Nat × SRType) :=
    match srtype with
    | 0b00 =>
      (let shift_t : SRType := SRType_LSL
      let shift_n : Nat := (BitVec.toNat imm5)
      (shift_n, shift_t))
    | 0b01 =>
      (let shift_t : SRType := SRType_LSR
      let shift_n : Nat :=
        if ((imm5 == 0b00000#5) : Bool)
        then 32
        else (BitVec.toNat imm5)
      (shift_n, shift_t))
    | 0b10 =>
      (let shift_t : SRType := SRType_ASR
      let shift_n : Nat :=
        if ((imm5 == 0b00000#5) : Bool)
        then 32
        else (BitVec.toNat imm5)
      (shift_n, shift_t))
    | _ =>
      (let (shift_n, shift_t) : (Nat × SRType) :=
        if ((imm5 == 0b00000#5) : Bool)
        then
          (let shift_t : SRType := SRType_RRX
          let shift_n : Nat := 1
          (shift_n, shift_t))
        else
          (let shift_t : SRType := SRType_ROR
          let shift_n : Nat := (BitVec.toNat imm5)
          (shift_n, shift_t))
      (shift_n, shift_t))
  let shift_n : Int := shift_n
  (pure ((shift_t, shift_n)))


def DecodeRegShift (srtype : (BitVec 2)) : SailM SRType := do
  let shift_t ← (( do (undefined_SRType (← occLabel 2702) ()) ) : SailM SRType )
  let shift_t : SRType :=
    match srtype with
    | 0b00 => SRType_LSL
    | 0b01 => SRType_LSR
    | 0b10 => SRType_ASR
    | _ => SRType_ROR
  (pure (shift_t))


def T32ExpandImm_C (imm12 : (BitVec 12)) (carry_in : (BitVec 1)) : SailM ((BitVec 32) × (BitVec 1)) := do
  let unrotated_value ← (( do (undefined_bitvector_at (← occLabel 2704) 32) ) : SailM
    (BitVec 32) )
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 2705) 32) ) : SailM (BitVec 32) )
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 2706) 1) ) : SailM (BitVec 1) )
  let (carry_out, imm32) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb imm12 11 10)) == 0b00#2) : Bool)
    then
      (let imm32 : (BitVec 32) :=
        match (BitVec.setWidth 2 (Sail.BitVec.extractLsb imm12 9 8)) with
        | 0b00 => (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb imm12 7 0) 32)
        | 0b01 =>
          (((0b00000000#8 +++ (Sail.BitVec.extractLsb imm12 7 0)) +++ 0b00000000#8) +++ (Sail.BitVec.extractLsb
              imm12 7 0))
        | 0b10 =>
          ((((Sail.BitVec.extractLsb imm12 7 0) +++ 0b00000000#8) +++ (Sail.BitVec.extractLsb imm12
                7 0)) +++ 0b00000000#8)
        | _ =>
          ((((Sail.BitVec.extractLsb imm12 7 0) +++ (Sail.BitVec.extractLsb imm12 7 0)) +++ (Sail.BitVec.extractLsb
                imm12 7 0)) +++ (Sail.BitVec.extractLsb imm12 7 0))
      let carry_out : (BitVec 1) := carry_in
      (pure ((carry_out, imm32))))
    else
      (do
        let unrotated_value : (BitVec 32) :=
          (Sail.BitVec.zeroExtend (1#1 +++ (Sail.BitVec.extractLsb imm12 6 0)) 32)
        let w__0 ← (( do
          (ROR_C unrotated_value (BitVec.toNat (Sail.BitVec.extractLsb imm12 11 7))) ) : SailM
          ((BitVec 32) × (BitVec 1)) )
        let (tup__0, tup__1) := (w__0 : ((BitVec 32) × (BitVec 1)))
        let imm32 : (BitVec 32) := tup__0
        let carry_out : (BitVec 1) := tup__1
        (pure ((carry_out, imm32)))) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (pure ((imm32, carry_out)))


/-- Type quantifiers: n : Int -/
def D_read (n : Int) : SailM (BitVec 64) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:41714.27-41714.28"
  let base : Nat := (Sail.Int.toNatChecked (((Nat.mod (Sail.Int.toNatChecked (n)) 2) *i 64)))
  let vreg ← (( do (V_read (Int.ediv (Sail.Int.toNatChecked (n)) 2) 128) ) : SailM (BitVec 128) )
  (pure ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb vreg
      (Sail.Int.toNatChecked ((base +i 63))) base))))


/-- Type quantifiers: processorid : Int, size : Int -/
def AArch32_IsExclusiveVA (address : (BitVec 32)) (processorid : Int) (size : Int) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: n : Int -/
def S_read (n : Int) : SailM (BitVec 32) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:42210.27-42210.28"
  let base : Nat := (Sail.Int.toNatChecked (((Nat.mod (Sail.Int.toNatChecked (n)) 4) *i 32)))
  let vreg ← (( do (V_read (Int.ediv (Sail.Int.toNatChecked (n)) 4) 128) ) : SailM (BitVec 128) )
  (pure ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb vreg
      (Sail.Int.toNatChecked ((base +i 31))) base))))


/-- Type quantifiers: n : Int -/
def Q_read (n : Int) : SailM (BitVec 128) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 15)) "sail-arm/v8_base.sail:42241.27-42241.28"
  (V_read n 128)


/-- Type quantifiers: n : Int -/
def Qin_read (n : Int) : SailM (BitVec 128) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 15)) "sail-arm/v8_base.sail:42446.27-42446.28"
  let w__0 ← (( do (Din_read ((2 *i n) +i 1)) ) : SailM (BitVec 64) )
  let w__1 ← (( do (Din_read (2 *i n)) ) : SailM (BitVec 64) )
  (pure ((w__0 +++ w__1)))


def ConditionPassed (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
  (ConditionHolds w__0)


def _set_ID_MMFR2_EL1_Type_HWAccFlg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_HWAccFlg r v)


def _set_ID_MMFR2_Type_HWAccFlg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_HWAccFlg r v)


def _set_ID_MMFR2_EL1_Type_HvdTLB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_HvdTLB r v)


def _set_ID_MMFR2_Type_HvdTLB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_HvdTLB r v)


def _set_ID_MMFR2_EL1_Type_L1HvdBG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_L1HvdBG r v)


def _set_ID_MMFR2_Type_L1HvdBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_L1HvdBG r v)


def _set_ID_MMFR2_EL1_Type_L1HvdFG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_L1HvdFG r v)


def _set_ID_MMFR2_Type_L1HvdFG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_L1HvdFG r v)


def _set_ID_MMFR2_EL1_Type_L1HvdRng (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_L1HvdRng r v)


def _set_ID_MMFR2_Type_L1HvdRng (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_L1HvdRng r v)


def _set_ID_MMFR2_EL1_Type_MemBarr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_MemBarr r v)


def _set_ID_MMFR2_Type_MemBarr (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_MemBarr r v)


def _set_ID_MMFR2_EL1_Type_UniTLB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_UniTLB r v)


def _set_ID_MMFR2_Type_UniTLB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_UniTLB r v)


def _set_ID_MMFR2_EL1_Type_WFIStall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_WFIStall r v)


def _set_ID_MMFR2_Type_WFIStall (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR2_Type_WFIStall r v)


def _set_ID_MMFR4_EL1_Type_AC2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_AC2 r v)


def _set_ID_MMFR4_Type_AC2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_AC2 r v)


def _set_ID_MMFR4_EL1_Type_CCIDX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_CCIDX r v)


end ArmFull.Functions
