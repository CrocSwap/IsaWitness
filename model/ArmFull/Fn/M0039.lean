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

def _update_HTCR_Type_IRGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_TCR_EL2_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_TCR_EL3_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_TTBCR_Type_IRGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_VTCR_EL2_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_VTCR_Type_IRGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _get_HTCR_Type_IRGN0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_TCR_EL2_Type_IRGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_TCR_EL3_Type_IRGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_TTBCR_Type_IRGN0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_VTCR_EL2_Type_IRGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_VTCR_Type_IRGN0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_TCR_EL1_Type_IRGN1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_TCR_EL1_Type_IRGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _update_TCR_EL2_Type_IRGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _update_TTBCR_Type_IRGN1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _get_TCR_EL2_Type_IRGN1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _get_TTBCR_Type_IRGN1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _get_TCR_EL1_Type_MTX0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_TCR_EL1_Type_MTX0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_TCR_EL2_Type_MTX0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_TCR_EL2_Type_MTX0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _get_TCR_EL1_Type_MTX1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_TCR_EL1_Type_MTX1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _update_TCR_EL2_Type_MTX1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _get_TCR_EL2_Type_MTX1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _get_TCR_EL1_Type_NFD0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)


def _update_TCR_EL1_Type_NFD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)


def _update_TCR_EL2_Type_NFD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)


def _get_TCR_EL2_Type_NFD0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)


def _get_TCR_EL1_Type_NFD1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _update_TCR_EL1_Type_NFD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _update_TCR_EL2_Type_NFD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _get_TCR_EL2_Type_NFD1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _get_TCR_EL1_Type_ORGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_TCR_EL1_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_HTCR_Type_ORGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_TCR_EL2_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_TCR_EL3_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_TTBCR_Type_ORGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_VTCR_EL2_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_VTCR_Type_ORGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_HTCR_Type_ORGN0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_TCR_EL2_Type_ORGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_TCR_EL3_Type_ORGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_TTBCR_Type_ORGN0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_VTCR_EL2_Type_ORGN0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_VTCR_Type_ORGN0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_TCR_EL1_Type_ORGN1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _update_TCR_EL1_Type_ORGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _update_TCR_EL2_Type_ORGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _update_TTBCR_Type_ORGN1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _get_TCR_EL2_Type_ORGN1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _get_TTBCR_Type_ORGN1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _get_TCR_EL1_Type_SH0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _update_TCR_EL1_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_HTCR_Type_SH0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_TCR_EL2_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_TCR_EL3_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_TTBCR_Type_SH0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_VTCR_EL2_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_VTCR_Type_SH0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _get_HTCR_Type_SH0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_TCR_EL2_Type_SH0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_TCR_EL3_Type_SH0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_TTBCR_Type_SH0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_VTCR_EL2_Type_SH0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_VTCR_Type_SH0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_TCR_EL1_Type_SH1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)


def _update_TCR_EL1_Type_SH1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)


def _update_TCR_EL2_Type_SH1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)


def _update_TTBCR_Type_SH1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 28 x)


def _get_TCR_EL2_Type_SH1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)


def _get_TTBCR_Type_SH1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)


def _get_TCR_EL1_Type_T0SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)


def _update_TCR_EL1_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)


def _update_HTCR_Type_T0SZ (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_TCR_EL2_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)


def _update_TCR_EL3_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)


def _update_TTBCR_Type_T0SZ (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_VSTCR_EL2_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)


def _update_VTCR_EL2_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)


def _update_VTCR_Type_T0SZ (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_HTCR_Type_T0SZ (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_TCR_EL2_Type_T0SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)


def _get_TCR_EL3_Type_T0SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)


def _get_TTBCR_Type_T0SZ (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_VSTCR_EL2_Type_T0SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)


def _get_VTCR_EL2_Type_T0SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)


def _get_VTCR_Type_T0SZ (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_TCR_EL1_Type_T1SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 21 16)


def _update_TCR_EL1_Type_T1SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 16 x)


def _update_TCR_EL2_Type_T1SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 16 x)


def _update_TTBCR_Type_T1SZ (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 16 x)


def _get_TCR_EL2_Type_T1SZ (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 21 16)


def _get_TTBCR_Type_T1SZ (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)


def _get_TCR_EL1_Type_TBI0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_TCR_EL1_Type_TBI0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_TCR_EL2_Type_TBI0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _get_TCR_EL2_Type_TBI0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _get_TCR_EL1_Type_TBI1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _update_TCR_EL1_Type_TBI1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _update_TCR_EL2_Type_TBI1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _get_TCR_EL2_Type_TBI1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _get_TCR_EL1_Type_TBID0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)


def _update_TCR_EL1_Type_TBID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)


def _update_TCR_EL2_Type_TBID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)


def _get_TCR_EL2_Type_TBID0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)


def _get_TCR_EL1_Type_TBID1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _update_TCR_EL1_Type_TBID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _update_TCR_EL2_Type_TBID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _get_TCR_EL2_Type_TBID1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _get_TCR_EL1_Type_TCMA0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


def _update_TCR_EL1_Type_TCMA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)


def _update_TCR_EL2_Type_TCMA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)


def _get_TCR_EL2_Type_TCMA0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


def _get_TCR_EL1_Type_TCMA1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_TCR_EL1_Type_TCMA1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _update_TCR_EL2_Type_TCMA1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _get_TCR_EL2_Type_TCMA1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _get_TCR_EL1_Type_TG0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_TCR_EL1_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_TCR_EL2_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_TCR_EL3_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_VSTCR_EL2_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_VTCR_EL2_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_TCR_EL2_Type_TG0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_TCR_EL3_Type_TG0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_VSTCR_EL2_Type_TG0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_VTCR_EL2_Type_TG0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_TCR_EL1_Type_TG1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _update_TCR_EL1_Type_TG1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _update_TCR_EL2_Type_TG1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _get_TCR_EL2_Type_TG1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def undefined_TCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TCR_EL2_Type_HPD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_TCR_EL2_Type_HPD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_HTCR_Type_HPD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_TCR_EL3_Type_HPD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_HTCR_Type_HPD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_TCR_EL3_Type_HPD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_TCR_EL2_Type_HWU59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_TCR_EL2_Type_HWU59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_HTCR_Type_HWU59 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_TCR_EL3_Type_HWU59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_VTCR_EL2_Type_HWU59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_VTCR_Type_HWU59 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_HTCR_Type_HWU59 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_TCR_EL3_Type_HWU59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_VTCR_EL2_Type_HWU59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_VTCR_Type_HWU59 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_TCR_EL2_Type_HWU60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_TCR_EL2_Type_HWU60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_HTCR_Type_HWU60 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_TCR_EL3_Type_HWU60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_VTCR_EL2_Type_HWU60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_VTCR_Type_HWU60 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_HTCR_Type_HWU60 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_TCR_EL3_Type_HWU60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_VTCR_EL2_Type_HWU60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_VTCR_Type_HWU60 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_TCR_EL2_Type_HWU61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_TCR_EL2_Type_HWU61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_HTCR_Type_HWU61 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_TCR_EL3_Type_HWU61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_VTCR_EL2_Type_HWU61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_VTCR_Type_HWU61 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_HTCR_Type_HWU61 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_TCR_EL3_Type_HWU61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_VTCR_EL2_Type_HWU61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_VTCR_Type_HWU61 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_TCR_EL2_Type_HWU62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_TCR_EL2_Type_HWU62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_HTCR_Type_HWU62 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_TCR_EL3_Type_HWU62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_VTCR_EL2_Type_HWU62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_VTCR_Type_HWU62 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_HTCR_Type_HWU62 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_TCR_EL3_Type_HWU62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_VTCR_EL2_Type_HWU62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_VTCR_Type_HWU62 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_TCR_EL2_Type_MTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _update_TCR_EL2_Type_MTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _update_TCR_EL3_Type_MTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _get_TCR_EL3_Type_MTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _get_TCR_EL2_Type_PS (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)


def _update_TCR_EL2_Type_PS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)


def _update_TCR_EL3_Type_PS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)


def _update_VTCR_EL2_Type_PS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)


def _get_TCR_EL3_Type_PS (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)


def _get_VTCR_EL2_Type_PS (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)


def _get_TCR_EL2_Type_TBI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_TCR_EL2_Type_TBI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_TCR_EL3_Type_TBI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_TCR_EL3_Type_TBI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_TCR_EL2_Type_TBID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_TCR_EL2_Type_TBID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_TCR_EL3_Type_TBID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_TCR_EL3_Type_TBID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


end ArmFull.Functions
