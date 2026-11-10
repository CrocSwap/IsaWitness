import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0004
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009

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

def _set_PMVIDSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMVIDSR_Type_bits r v)


def _set_PMXEVCNTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMXEVCNTR_EL0_Type_bits r v)


def _set_PMZR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMZR_EL0_Type_bits r v)


def _set_POR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_POR_EL0_Type_bits r v)


def _set_POR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_POR_EL1_Type_bits r v)


def _set_POR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_POR_EL2_Type_bits r v)


def _set_POR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_POR_EL3_Type_bits r v)


def _set_PRRR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_bits r v)


def _set_RCWMASK_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_RCWMASK_EL1_Type_bits r v)


def _set_RCWSMASK_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_RCWSMASK_EL1_Type_bits r v)


def _set_RGSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RGSR_EL1_Type_bits r v)


def _set_RMR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL1_Type_bits r v)


def _set_RMR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL2_Type_bits r v)


def _set_RMR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL3_Type_bits r v)


def _set_RMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_RMR_Type_bits r v)


def _set_RNDRRS_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RNDRRS_Type_bits r v)


def _set_RNDR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RNDR_Type_bits r v)


def _set_RVBAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RVBAR_EL1_Type_bits r v)


def _set_RVBAR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RVBAR_EL2_Type_bits r v)


def _set_RVBAR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RVBAR_EL3_Type_bits r v)


def _set_S1PIRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_S1PIRType_bits r v)


def _set_S1PORType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_S1PORType_bits r v)


def _set_S2PIRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_S2PIRType_bits r v)


def _set_S2PIR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_S2PIR_EL2_Type_bits r v)


def _set_S2POR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_S2POR_EL1_Type_bits r v)


def _set_SCRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCRType_bits r v)


def _set_SCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_bits r v)


def _set_SCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCR_Type_bits r v)


def _set_SCTLR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_bits r v)


def _set_SCTLR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_bits r v)


def _set_SCTLR2_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_bits r v)


def _set_SCTLRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLRType_bits r v)


def _set_SCTLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_bits r v)


def _set_SCTLR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_bits r v)


def _set_SCTLR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_bits r v)


def _set_SCTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_bits r v)


def _set_SDCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDCR_Type_bits r v)


def _set_SDER32_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SDER32_EL2_Type_bits r v)


def _set_SDER32_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SDER32_EL3_Type_bits r v)


def _set_SDER_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDER_Type_bits r v)


def _set_SMCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL1_Type_bits r v)


def _set_SMCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL2_Type_bits r v)


def _set_SMCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL3_Type_bits r v)


def _set_SMIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMIDR_EL1_Type_bits r v)


def _set_SMPRIMAP_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_bits r v)


def _set_SMPRI_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMPRI_EL1_Type_bits r v)


def _set_SPMACCESSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_bits r v)


def _set_SPMACCESSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_bits r v)


def _set_SPMACCESSR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_bits r v)


def _set_SPMSELR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMSELR_EL0_Type_bits r v)


def _set_SPSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL1_Type_bits r v)


def _set_SPSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL2_Type_bits r v)


def _set_SPSR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL3_Type_bits r v)


def _set_SPSR_abt_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_abt_Type_bits r v)


def _set_SPSR_fiq_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_fiq_Type_bits r v)


def _set_SPSR_hyp_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_hyp_Type_bits r v)


def _set_SPSR_irq_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_bits r v)


def _set_SPSR_mon_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_bits r v)


def _set_SPSR_svc_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_bits r v)


def _set_SPSR_und_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_bits r v)


def _set_TCR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_bits r v)


def _set_TCR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_bits r v)


def _set_TCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL1_Type_bits r v)


def _set_TCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL2_Type_bits r v)


def _set_TCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_bits r v)


def _set_TFSRE0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSRE0_EL1_Type_bits r v)


def _set_TFSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL1_Type_bits r v)


def _set_TFSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL2_Type_bits r v)


def _set_TFSR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL3_Type_bits r v)


def _set_TLBTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TLBTR_Type_bits r v)


def _set_TRFCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL1_Type_bits r v)


def _set_TRFCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL2_Type_bits r v)


def _set_TRFCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TRFCR_Type_bits r v)


def _set_TTBCR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR2_Type_bits r v)


def _set_TTBCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR_Type_bits r v)


def _set_TTBR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL1_Type_bits r v)


def _set_TTBR0_EL2_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL2_Type_bits r v)


def _set_TTBR0_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_EL3_Type_bits r v)


def _set_TTBR0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_bits r v)


def _set_TTBR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL1_Type_bits r v)


def _set_TTBR1_EL2_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL2_Type_bits r v)


def _set_TTBR1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_bits r v)


def _set_VDFSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDFSR_Type_bits r v)


def _set_VDISR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_bits r v)


def _set_VDISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDISR_Type_bits r v)


def _set_VMECID_A_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMECID_A_EL2_Type_bits r v)


def _set_VMECID_P_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMECID_P_EL2_Type_bits r v)


def _set_VMPIDR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_bits r v)


def _set_VMPIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VMPIDR_Type_bits r v)


def _set_VNCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VNCR_EL2_Type_bits r v)


def _set_VPIDR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VPIDR_EL2_Type_bits r v)


def _set_VPIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VPIDR_Type_bits r v)


def _set_VSESR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSESR_EL2_Type_bits r v)


def _set_VSTCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTCR_EL2_Type_bits r v)


def _set_VSTTBR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTTBR_EL2_Type_bits r v)


def _set_VTCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_bits r v)


def _set_VTCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VTCR_Type_bits r v)


def _set_VTTBR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_VTTBR_EL2_Type_bits r v)


def _set_VTTBR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTTBR_Type_bits r v)


def _set_ZCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ZCR_EL1_Type_bits r v)


def _set_ZCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ZCR_EL2_Type_bits r v)


def _set_ZCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ZCR_EL3_Type_bits r v)


def _set_Configuration_Type_CFGEND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_CFGEND r v)


def _set_Configuration_Type_CONFIG64 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_CONFIG64 r v)


def _set_Configuration_Type_CfgNMFI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_CfgNMFI r v)


def _set_Configuration_Type_Cp15SDisable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_Cp15SDisable r v)


def _set_Configuration_Type_Cp15SDisable2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_Cp15SDisable2 r v)


def _set_Configuration_Type_ExceptInit (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_ExceptInit r v)


def _set_Configuration_Type_HIVECS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_HIVECS r v)


def _set_Configuration_Type_RW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_RW r v)


def _set_EDSCR_Type_RW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_RW r v)


def _set_HCR_EL2_Type_RW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_RW r v)


def _set_SCRType_RW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCRType_RW r v)


def _set_SCR_EL3_Type_RW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_RW r v)


def _set_Configuration_Type_disableNIDebug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_disableNIDebug r v)


def _set_Configuration_Type_disableSPIDebug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_disableSPIDebug r v)


def _set_Configuration_Type_disableSPNIDebug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_disableSPNIDebug r v)


def _set_DormantCtl_Type_Dbgnopwrdwn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_Dbgnopwrdwn r v)


def _set_DormantCtl_Type_PowerDownStatusSupport (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_PowerDownStatusSupport r v)


def _set_DormantCtl_Type_ResetCatchStatus (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_ResetCatchStatus r v)


def _set_DormantCtl_Type_TestResetCatch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_TestResetCatch r v)


def _set_DormantCtl_Type_dbgpwrupreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_dbgpwrupreq r v)


def _set_DormantCtl_Type_dbgrstreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_dbgrstreq r v)


def _set_DormantCtl_Type_etmpwrdwnreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_etmpwrdwnreq r v)


def _set_DormantCtl_Type_etmpwrupreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_etmpwrupreq r v)


def _set_DormantCtl_Type_nDbgpwrdwnreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_nDbgpwrdwnreq r v)


def _set_DormantCtl_Type_nPU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_nPU r v)


def _set_DormantCtl_Type_standbywfe (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_standbywfe r v)


def _set_DormantCtl_Type_standbywfi (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DormantCtl_Type_standbywfi r v)


def HaveAArch32EL (el : (BitVec 2)) : Bool :=
  (el == EL0)


def IsFeatureImplemented (feat : Feature) : SailM Bool := do
  let w__0 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  (pure ((GetElem?.getElem! w__0 (Sail.Int.toNatChecked ((num_of_Feature feat))))))


def InitVariantImplemented (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__1 ← (( do readReg v8Ap0_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__0
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap0))) w__1)
  let w__2 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__3 ← (( do readReg v8Ap1_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__2
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap1))) w__3)
  let w__4 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__5 ← (( do readReg v8Ap2_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__4
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap2))) w__5)
  let w__6 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__7 ← (( do readReg v8Ap3_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__6
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap3))) w__7)
  let w__8 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__9 ← (( do readReg v8Ap4_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__8
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap4))) w__9)
  let w__10 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__11 ← (( do readReg v8Ap5_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__10
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap5))) w__11)
  let w__12 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__13 ← (( do readReg v8Ap6_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__12
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap6))) w__13)
  let w__14 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__15 ← (( do readReg v8Ap7_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__14
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap7))) w__15)
  let w__16 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__17 ← (( do readReg v8Ap8_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__16
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap8))) w__17)
  let w__18 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__19 ← (( do readReg v8Ap9_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__18
    (Sail.Int.toNatChecked ((num_of_ArchVersion v8Ap9))) w__19)
  let w__20 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__21 ← (( do readReg v9Ap0_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__20
    (Sail.Int.toNatChecked ((num_of_ArchVersion v9Ap0))) w__21)
  let w__22 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__23 ← (( do readReg v9Ap1_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__22
    (Sail.Int.toNatChecked ((num_of_ArchVersion v9Ap1))) w__23)
  let w__24 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__25 ← (( do readReg v9Ap2_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__24
    (Sail.Int.toNatChecked ((num_of_ArchVersion v9Ap2))) w__25)
  let w__26 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__27 ← (( do readReg v9Ap3_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__26
    (Sail.Int.toNatChecked ((num_of_ArchVersion v9Ap3))) w__27)
  let w__28 ← (( do readReg VariantImplemented ) : SailM (Vector Bool 16) )
  let w__29 ← (( do readReg v9Ap4_IMPLEMENTED ) : SailM Bool )
  writeReg VariantImplemented (vectorUpdate w__28
    (Sail.Int.toNatChecked ((num_of_ArchVersion v9Ap4))) w__29)


def _set_SCRType_AW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCRType_AW r v)


def _set_SCR_Type_AW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCR_Type_AW r v)


def _set_SCRType_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCRType_EA r v)


def _set_DISR_EL1_Type_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DISR_EL1_Type_EA r v)


end ArmFull.Functions
