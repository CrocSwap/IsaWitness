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

def _update_GICC_AHPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_AIAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_BPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_EOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_HPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_IAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_CLRSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_CLRSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_SETSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_SETSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_SGIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_TYPER2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICD_TYPER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICH_EISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICH_ELRSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICH_HCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICH_MISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICH_VMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICH_VTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICM_CLRSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICM_CLRSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICM_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICM_SETSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICM_SETSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICM_TYPER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_CLRLPIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_INMIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_INVALLR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_INVLPIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_ISENABLER0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_MPAMIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_PARTIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_PENDBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_PROPBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_SETLPIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_SYNCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_VPENDBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_VPROPBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICR_VSGIPENDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_VSGIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICR_WAKER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_ABPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_AEOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_AHPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_AIAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_BPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_EOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_HPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_IAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICV_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_CBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GITS_CREADR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GITS_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_CWRITER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GITS_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_MPAMIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_MPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_PARTIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_SGIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GITS_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GITS_TYPER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GMID_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GPCCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GPTBR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HAFGRTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HCPTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HCR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HCRX_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HDCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HDFGRTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HDFGRTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HDFGWTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HDFGWTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HFGITR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HFGRTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HFGRTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HFGWTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HFGWTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HMAIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HMAIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HPFAR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HPFAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HRMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HSCTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HSTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_HSTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HTCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HTRFCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_HTTBR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_AP1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_ASGI1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_ASGI1R_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_BPR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_BPR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_BPR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_BPR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_CTLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_CTLR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_DIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_EOIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_EOIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_EOIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_EOIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_HPPIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_HPPIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_HPPIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_HPPIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_HSRE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_IAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_IAR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_IAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_IAR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_IGRPEN0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_IGRPEN1_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_IGRPEN1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_MCTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_MGRPEN1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_MSRE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_NMIAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_PMR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_RPR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICC_SGI0R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SGI0R_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SGI1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SGI1R_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SRE_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SRE_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SRE_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICC_SRE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_AP0R_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_AP0R_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_AP1R_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_AP1R_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_EISR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_EISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_ELRSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_ELRSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_HCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_HCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_LRC_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_LR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_LR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_MISR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_MISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_VMCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_VMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICH_VTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICH_VTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_AP1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_BPR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_BPR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_BPR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_BPR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_CTLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_DIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_EOIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_EOIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_EOIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_EOIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_HPPIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_HPPIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_HPPIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_HPPIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_IAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_IAR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_IAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_IAR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_IGRPEN0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_IGRPEN1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ICV_NMIAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_PMR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


end ArmFull.Functions
