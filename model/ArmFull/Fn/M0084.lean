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

def _get_CTICIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_PMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def Mk_GICM_SETSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICR_WAKER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICR_WAKER_Type_ChildrenAsleep (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_GICR_WAKER_Type_ChildrenAsleep (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GICR_WAKER_Type_ProcessorSleep (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_GICR_WAKER_Type_ProcessorSleep (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def Mk_GITS_PARTIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GITS_PARTIDR_Type_PARTID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_GITS_PARTIDR_Type_PARTID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_GICR_PARTIDR_Type_PARTID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_GICR_PARTIDR_Type_PARTID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_GITS_PARTIDR_Type_PMG (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _update_GITS_PARTIDR_Type_PMG (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_GICR_PARTIDR_Type_PMG (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _get_GICR_PARTIDR_Type_PMG (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def Mk_GICV_HPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTIPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_CTIPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_AMPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_EDPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_PMPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_AMPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_EDPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_PMPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def Mk_GICM_SETSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_EDPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_AMPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_CTIPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_PMPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_AMPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_CTIPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_PMPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_EDPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_EDPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_AMPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_CTIPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_PMPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_AMPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_CTIPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_PMPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def Mk_GICC_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICC_STATUSR_Type_ASV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_GICC_STATUSR_Type_ASV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GICC_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GICC_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICD_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICR_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICV_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GITS_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICD_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_GICR_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_GICV_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_GITS_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_GICC_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_GICC_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GICD_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GICR_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GICV_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GITS_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GICD_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_GICR_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_GICV_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_GITS_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_GICC_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_GICC_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICD_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICR_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICV_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GITS_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICD_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_GICR_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_GICV_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_GITS_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_GICC_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_GICC_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICD_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICR_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICV_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GITS_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_GICD_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_GICR_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_GICV_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_GITS_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def Mk_GICM_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICR_VSGIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICM_TYPER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICM_TYPER_Type_CLR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_GICM_TYPER_Type_CLR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_GICM_TYPER_Type_NumSPIs (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 10 0)


def _update_GICM_TYPER_Type_NumSPIs (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 0 x)


def Mk_GICD_TYPER2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICD_TYPER2_Type_VID (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_GICD_TYPER2_Type_VID (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _get_GICD_TYPER2_Type_VIL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_GICD_TYPER2_Type_VIL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_GICD_TYPER2_Type_nASSGIcap (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_GICD_TYPER2_Type_nASSGIcap (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def Mk_GICH_EISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICH_ELRSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICM_CLRSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICM_CLRSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_AEOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_ABPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICV_ABPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _update_GICV_ABPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_GICC_ABPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_GICC_BPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_GICV_BPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _get_GICC_ABPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_GICC_BPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_GICV_BPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def Mk_CTIDEVARCH_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIDEVARCH_Type_ARCHID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_CTIDEVARCH_Type_ARCHID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_AMDEVARCH_Type_ARCHID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_AMDEVARCH_Type_ARCHID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def Mk_GICR_MPAMIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICR_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_GICR_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_GITS_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_GITS_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_GICR_MPAMIDR_Type_PMGmax (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _update_GICR_MPAMIDR_Type_PMGmax (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_GITS_MPAMIDR_Type_PMGmax (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _get_GITS_MPAMIDR_Type_PMGmax (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def Mk_CTICIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_AIAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_AHPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICR_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICR_CTLR_Type_CES (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_GICR_CTLR_Type_CES (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICR_CTLR_Type_DPG0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_GICR_CTLR_Type_DPG0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_GICR_CTLR_Type_DPG1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_GICR_CTLR_Type_DPG1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_GICR_CTLR_Type_DPG1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_GICR_CTLR_Type_DPG1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_GICR_CTLR_Type_EnableLPIs (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GICR_CTLR_Type_EnableLPIs (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICR_CTLR_Type_UWP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_GICR_CTLR_Type_UWP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def Mk_CNTEL0ACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_BPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICV_EOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTFID0_Type_Frequency (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_CNTFID0_Type_Frequency (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def Mk_GICD_TYPER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICD_TYPER_Type_CPUNumber (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 7 5)


def _update_GICD_TYPER_Type_CPUNumber (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 5 x)


def _get_GICD_TYPER_Type_DVIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_GICD_TYPER_Type_DVIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_GICD_TYPER_Type_ESPI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_GICD_TYPER_Type_ESPI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_GICD_TYPER_Type_ESPI_range (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)


def _update_GICD_TYPER_Type_ESPI_range (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 27 x)


def _get_GICD_TYPER_Type_ITLinesNumber (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_GICD_TYPER_Type_ITLinesNumber (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _get_GICD_TYPER_Type_LPIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_GICD_TYPER_Type_LPIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_GICD_TYPER_Type_MBIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_GICD_TYPER_Type_MBIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_GICD_TYPER_Type_No1N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_GICD_TYPER_Type_No1N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_GICD_TYPER_Type_SecurityExtn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_GICD_TYPER_Type_SecurityExtn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_GICD_TYPER_Type_num_LPIs (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 15 11)


def _update_GICD_TYPER_Type_num_LPIs (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 11 x)


def Mk_CTICIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTICIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_CTICIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_AMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_EDCIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_PMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_AMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_EDCIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_PMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def Mk_GICC_HPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICD_CLRSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTIITCTRL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIITCTRL_Type_IME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_CTIITCTRL_Type_IME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_EDITCTRL_Type_IME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMITCTRL_Type_IME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_EDITCTRL_Type_IME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMITCTRL_Type_IME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def Mk_GITS_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GITS_STATUSR_Type_Overflow (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_GITS_STATUSR_Type_Overflow (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


end ArmFull.Functions
