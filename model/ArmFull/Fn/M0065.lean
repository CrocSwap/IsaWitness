module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork set_option backward.proofsInPublic true @[expose] public section

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

def _get_HDFGWTR_EL2_Type_TRCSSCSRn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)


def _get_HDFGRTR_EL2_Type_TRCSTATR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)


def _update_HDFGRTR_EL2_Type_TRCSTATR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)


def _get_HDFGRTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)


def _update_HDFGRTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)


def _update_HDFGWTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)


def _get_HDFGWTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)


def _get_HDFGRTR_EL2_Type_nBRBCTL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_HDFGRTR_EL2_Type_nBRBCTL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_HDFGWTR_EL2_Type_nBRBCTL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_HDFGWTR_EL2_Type_nBRBCTL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _get_HDFGRTR_EL2_Type_nBRBDATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_HDFGRTR_EL2_Type_nBRBDATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _update_HDFGWTR_EL2_Type_nBRBDATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _get_HDFGWTR_EL2_Type_nBRBDATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _get_HDFGRTR_EL2_Type_nBRBIDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _update_HDFGRTR_EL2_Type_nBRBIDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _update_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _get_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def Mk_ICV_NMIAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICV_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _update_ICV_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_AEOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_AHPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_AIAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_EOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_HPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICC_IAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_GICD_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICD_CLRSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICD_SETSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICD_SETSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICD_SGIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_GICM_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICM_CLRSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICM_SETSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICM_SETSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _update_GICM_TYPER_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 16 x)


def _update_GICR_INVLPIR_Type_INTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_GICV_AEOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_GICV_AHPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_GICV_AIAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_GICV_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_GICV_EOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_GICV_HPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_GICV_IAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)


def _update_ICC_ASGI1R_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ICC_ASGI1R_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ICC_DIR_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_EOIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_EOIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_EOIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_EOIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_HPPIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_HPPIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_IAR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_IAR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_IAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_IAR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICC_SGI0R_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ICC_SGI0R_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ICC_SGI1R_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ICC_SGI1R_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ICV_DIR_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_EOIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_EOIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_EOIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_EOIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_HPPIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_HPPIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_IAR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_IAR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_IAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_ICV_IAR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _get_GICC_AEOIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICC_AHPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICC_AIAR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICC_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICC_EOIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICC_HPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICC_IAR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_GICD_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICD_CLRSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICD_SETSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICD_SETSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICD_SGIR_Type_INTID (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_GICM_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICM_CLRSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICM_SETSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICM_SETSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_GICM_TYPER_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 28 16)


def _get_GICR_INVLPIR_Type_INTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _get_GICV_AEOIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_GICV_AHPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_GICV_AIAR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_GICV_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_GICV_EOIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_GICV_HPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_GICV_IAR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)


def _get_ICC_ASGI1R_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ICC_ASGI1R_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ICC_DIR_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_EOIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_EOIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_EOIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_EOIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_HPPIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_HPPIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_IAR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_IAR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_IAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_IAR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICC_SGI0R_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ICC_SGI0R_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ICC_SGI1R_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ICC_SGI1R_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ICV_DIR_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_EOIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_EOIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_EOIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_EOIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_HPPIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_HPPIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_IAR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_IAR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_IAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_ICV_IAR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def undefined_ICH_LR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ICH_LR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICH_LR_EL2_Type_Group (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_ICH_LR_EL2_Type_Group (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_ICH_LRC_Type_Group (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_ICH_LRC_Type_Group (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_ICH_LR_EL2_Type_HW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_ICH_LR_EL2_Type_HW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _update_ICH_LRC_Type_HW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_ICH_LRC_Type_HW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_ICH_LR_EL2_Type_State (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)


def _update_ICH_LR_EL2_Type_State (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)


def _update_ICH_LRC_Type_State (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _get_ICH_LRC_Type_State (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _get_ICH_LR_EL2_Type_pINTID (v : (BitVec 64)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 44 32)


def _update_ICH_LR_EL2_Type_pINTID (v : (BitVec 64)) (x : (BitVec 13)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 32 x)


def _update_GICR_CLRLPIR_Type_pINTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_GICR_SETLPIR_Type_pINTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_ICH_LRC_Type_pINTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)


def _get_GICR_CLRLPIR_Type_pINTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _get_GICR_SETLPIR_Type_pINTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _get_ICH_LRC_Type_pINTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)


def _get_ICH_LR_EL2_Type_vINTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_ICH_LR_EL2_Type_vINTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_GITS_SGIR_Type_vINTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ICH_LR_Type_vINTID (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_GITS_SGIR_Type_vINTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ICH_LR_Type_vINTID (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def Mk_MVFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MVFR0_EL1_Type_FPDP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_MVFR0_EL1_Type_FPDP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_MVFR0_Type_FPDP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_MVFR0_EL1_Type_FPDivide (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_MVFR0_EL1_Type_FPDivide (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_MVFR0_Type_FPDivide (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_MVFR0_EL1_Type_FPRound (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_MVFR0_EL1_Type_FPRound (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_MVFR0_Type_FPRound (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_MVFR0_EL1_Type_FPSP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_MVFR0_EL1_Type_FPSP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_MVFR0_Type_FPSP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_MVFR0_EL1_Type_FPShVec (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_MVFR0_EL1_Type_FPShVec (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_MVFR0_Type_FPShVec (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_MVFR0_EL1_Type_FPSqrt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_MVFR0_EL1_Type_FPSqrt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_MVFR0_Type_FPSqrt (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_MVFR0_EL1_Type_FPTrap (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_MVFR0_EL1_Type_FPTrap (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_MVFR0_Type_FPTrap (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_MVFR0_EL1_Type_SIMDReg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_MVFR0_EL1_Type_SIMDReg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_MVFR0_Type_SIMDReg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def Mk_ICC_HPPIR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_AA64DFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64DFR0_EL1_Type_BRBE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


end ArmFull.Functions
