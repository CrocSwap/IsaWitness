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

def _get_ID_ISAR1_Type_Immediate (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_ISAR1_EL1_Type_Interwork (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_ISAR1_EL1_Type_Interwork (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_ISAR1_Type_Interwork (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_ISAR1_EL1_Type_Jazelle (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_ISAR1_EL1_Type_Jazelle (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_ISAR1_Type_Jazelle (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def Mk_PMUACR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_RMR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMSELR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSELR_EL0_Type_SEL (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_PMSELR_EL0_Type_SEL (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _update_ERRSELR_EL1_Type_SEL (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ERRSELR_Type_SEL (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_PMSELR_Type_SEL (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _get_ERRSELR_EL1_Type_SEL (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_ERRSELR_Type_SEL (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_PMSELR_Type_SEL (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _get_ICC_CTLR_EL1_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_GICD_TYPER_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_GICH_VTR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_ICC_CTLR_EL3_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICC_CTLR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICC_MCTLR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICH_VTR_EL2_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_ICH_VTR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_ICV_CTLR_EL1_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICV_CTLR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_GICD_TYPER_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_GICH_VTR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_ICC_CTLR_EL3_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_ICC_CTLR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_ICC_MCTLR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_ICH_VTR_EL2_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_ICH_VTR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_ICV_CTLR_EL1_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_ICV_CTLR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_ICC_CTLR_EL1_Type_CBPR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICC_CTLR_EL1_Type_CBPR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICC_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_GICV_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_ICC_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICV_CTLR_EL1_Type_CBPR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICV_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICC_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_GICV_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICC_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICV_CTLR_EL1_Type_CBPR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICV_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_CTLR_EL1_Type_EOImode (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_ICC_CTLR_EL1_Type_EOImode (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICC_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_GICV_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_ICC_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICV_CTLR_EL1_Type_EOImode (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICV_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICC_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_GICV_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_ICC_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICV_CTLR_EL1_Type_EOImode (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICV_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_ICC_CTLR_EL3_Type_ExtRange (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ICC_CTLR_Type_ExtRange (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ICC_MCTLR_Type_ExtRange (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ICV_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ICV_CTLR_Type_ExtRange (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_ICC_CTLR_EL3_Type_ExtRange (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_ICC_CTLR_Type_ExtRange (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_ICC_MCTLR_Type_ExtRange (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_ICV_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_ICV_CTLR_Type_ExtRange (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_ICC_CTLR_EL1_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)


def _update_GICD_TYPER_Type_IDbits (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 19 x)


def _update_GICH_VTR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 23 x)


def _update_GICR_PROPBASER_Type_IDbits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _update_GICR_VPROPBASER_Type_IDbits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _update_ICC_CTLR_EL3_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 11 x)


def _update_ICC_CTLR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 11 x)


def _update_ICC_MCTLR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 11 x)


def _update_ICH_VTR_EL2_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 23 x)


def _update_ICH_VTR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 23 x)


def _update_ICV_CTLR_EL1_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 11 x)


def _update_ICV_CTLR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 11 x)


def _get_GICD_TYPER_Type_IDbits (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 23 19)


def _get_GICH_VTR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)


def _get_GICR_PROPBASER_Type_IDbits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _get_GICR_VPROPBASER_Type_IDbits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _get_ICC_CTLR_EL3_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)


def _get_ICC_CTLR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)


def _get_ICC_MCTLR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)


def _get_ICH_VTR_EL2_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)


def _get_ICH_VTR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)


def _get_ICV_CTLR_EL1_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)


def _get_ICV_CTLR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)


def _get_ICC_CTLR_EL1_Type_PMHE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_ICC_CTLR_EL1_Type_PMHE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ICC_CTLR_EL3_Type_PMHE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ICC_CTLR_Type_PMHE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ICC_MCTLR_Type_PMHE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_ICC_CTLR_EL3_Type_PMHE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ICC_CTLR_Type_PMHE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ICC_MCTLR_Type_PMHE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ICC_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _update_GICH_VTR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 29 x)


def _update_ICC_CTLR_EL3_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _update_ICC_CTLR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _update_ICC_MCTLR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _update_ICH_VTR_EL2_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 29 x)


def _update_ICH_VTR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 29 x)


def _update_ICV_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _update_ICV_CTLR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _get_GICH_VTR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 31 29)


def _get_ICC_CTLR_EL3_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _get_ICC_CTLR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _get_ICC_MCTLR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _get_ICH_VTR_EL2_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 31 29)


def _get_ICH_VTR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 31 29)


def _get_ICV_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _get_ICV_CTLR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _get_ICC_CTLR_EL1_Type_RSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_ICC_CTLR_EL1_Type_RSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_GICD_TYPER_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_ICC_CTLR_EL3_Type_RSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_ICC_CTLR_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_ICC_MCTLR_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_ICV_CTLR_EL1_Type_RSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_ICV_CTLR_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_GICD_TYPER_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_ICC_CTLR_EL3_Type_RSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICC_CTLR_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICC_MCTLR_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICV_CTLR_EL1_Type_RSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICV_CTLR_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICC_CTLR_EL1_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_ICC_CTLR_EL1_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_GICH_VTR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_GITS_TYPER_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_ICC_CTLR_EL3_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ICC_CTLR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ICC_MCTLR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ICH_VTR_EL2_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_ICH_VTR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_ICV_CTLR_EL1_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ICV_CTLR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_GICH_VTR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_GITS_TYPER_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICC_CTLR_EL3_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_ICC_CTLR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_ICC_MCTLR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_ICH_VTR_EL2_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_ICH_VTR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_ICV_CTLR_EL1_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_ICV_CTLR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def Mk_ID_ISAR6_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_ISAR6_EL1_Type_CLRBHB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_ISAR6_EL1_Type_CLRBHB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_AA64ISAR2_EL1_Type_CLRBHB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_ISAR6_Type_CLRBHB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_AA64ISAR2_EL1_Type_CLRBHB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_ISAR6_Type_CLRBHB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def undefined_ICC_AP1R_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ICC_AP1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def __set_CNTP_CTL_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTP_CTL_EL0_Type := value_name
  let w__0 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__0 1 0 (BitVec.slice r 0 2))
  let w__1 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__1 63 3 (BitVec.slice r 3 61))


def Mk_CNTHV_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICH_MISR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICH_MISR_EL2_Type_EOI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICH_MISR_EL2_Type_EOI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICH_MISR_Type_EOI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICH_MISR_Type_EOI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICH_MISR_Type_EOI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICH_MISR_EL2_Type_LRENP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_ICH_MISR_EL2_Type_LRENP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GICH_MISR_Type_LRENP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GICH_MISR_Type_LRENP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICH_MISR_Type_LRENP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICH_MISR_EL2_Type_NP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_ICH_MISR_EL2_Type_NP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICH_MISR_Type_NP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_GICH_MISR_Type_NP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICH_MISR_Type_NP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICH_MISR_EL2_Type_VGrp0D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_ICH_MISR_EL2_Type_VGrp0D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_GICH_MISR_Type_VGrp0D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_GICH_MISR_Type_VGrp0D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_ICH_MISR_Type_VGrp0D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_ICH_MISR_EL2_Type_VGrp0E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_ICH_MISR_EL2_Type_VGrp0E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_GICH_MISR_Type_VGrp0E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GICH_MISR_Type_VGrp0E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICH_MISR_Type_VGrp0E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICH_MISR_EL2_Type_VGrp1D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_ICH_MISR_EL2_Type_VGrp1D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_GICH_MISR_Type_VGrp1D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_GICH_MISR_Type_VGrp1D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_ICH_MISR_Type_VGrp1D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_ICH_MISR_EL2_Type_VGrp1E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_ICH_MISR_EL2_Type_VGrp1E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_GICH_MISR_Type_VGrp1E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


end ArmFull.Functions
