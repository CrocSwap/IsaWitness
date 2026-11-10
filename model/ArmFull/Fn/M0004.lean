import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

def _update_PMSNEVFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSWINC_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSWINC_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMUACR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMUSERENR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMUSERENR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMVCIDSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMVIDSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMXEVCNTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMZR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_POR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_POR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_POR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_POR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PRRR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_RCWMASK_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_RCWSMASK_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_RGSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RMR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RMR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RMR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_RNDRRS_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RNDR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RVBAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RVBAR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_RVBAR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_S1PIRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_S1PORType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_S2PIRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_S2PIR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_S2POR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SCTLR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLR2_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SCTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SDCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SDER32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SDER32_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SDER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SMCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SMCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SMCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SMIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SMPRIMAP_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SMPRI_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPMACCESSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPMACCESSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPMACCESSR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPMSELR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_abt_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_fiq_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_hyp_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SPSR_irq_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_SPSR_mon_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SPSR_svc_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_SPSR_und_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TCR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TCR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TFSRE0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TFSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TFSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TFSR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TLBTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_TRFCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TRFCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TRFCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_TTBCR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_TTBCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_TTBR0_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_TTBR0_EL2_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_TTBR0_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TTBR0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_TTBR1_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_TTBR1_EL2_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_TTBR1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VDFSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_VDISR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VDISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_VMECID_A_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VMECID_P_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VMPIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VMPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_VNCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VPIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_VSESR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VSTCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VSTTBR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VTCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_VTCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_VTTBR_EL2_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_VTTBR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ZCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ZCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ZCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _get_ACCDATA_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCFGR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCFGR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCG1IDR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCGCR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCGCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCNTENCLR0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCNTENCLR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCNTENCLR1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCNTENCLR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCNTENSET0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCNTENSET0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCNTENSET1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCNTENSET1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMCR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMDEVARCH_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMDEVTYPE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMEVCNTR0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMEVCNTR0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMEVCNTR1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMEVCNTR1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMEVTYPER0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMEVTYPER0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMEVTYPER1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMEVTYPER1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMIIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMPIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMPIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMPIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMPIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMPIDR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_AMUSERENR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_AMUSERENR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_BRBCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBFCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBIDR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBINFINJ_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBINFType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBINF_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBSRCINJ_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBSRCType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBSRC_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBTGTINJ_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBTGTType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBTGT_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_BRBTS_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CCSIDR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CCSIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CCSIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CCSIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CLIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CLIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTEL0ACR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTFID0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTHCTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHCTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTHPS_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHPS_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTHPS_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHPS_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHP_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHP_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTHP_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHP_CVAL_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHP_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHVS_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHVS_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTHVS_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHVS_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHV_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHV_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTHV_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTHV_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTKCTL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTKCTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTNSAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTPS_CTL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTPS_CVAL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTPS_TVAL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTP_CTL_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_CNTP_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_CNTP_CVAL_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


end ArmFull.Functions
