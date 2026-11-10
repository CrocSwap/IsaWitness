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

def _get_ID_AA64PFR0_EL1_Type_SEL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _update_ID_AA64PFR0_EL1_Type_SEL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def _update_EDPFR_Type_SEL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def _get_EDPFR_Type_SEL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _get_ID_AA64PFR0_EL1_Type_SVE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_ID_AA64PFR0_EL1_Type_SVE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _update_EDPFR_Type_SVE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_EDPFR_Type_SVE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def undefined_ICH_AP1R_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ICH_AP1R_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_DIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PMEVCNTSVR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMEVCNTSVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMEVCNTSVR_EL1_Type_EVCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _update_PMEVCNTSVR_EL1_Type_EVCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def Mk_ID_AA64ISAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64ISAR0_EL1_Type_AES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64ISAR0_EL1_Type_AES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_AA64ZFR0_EL1_Type_AES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR5_EL1_Type_AES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_AA64ZFR0_EL1_Type_AES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_ISAR5_EL1_Type_AES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_ISAR5_Type_AES (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_AA64ISAR0_EL1_Type_Atomic (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_AA64ISAR0_EL1_Type_Atomic (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_AA64ISAR0_EL1_Type_CRC32 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64ISAR0_EL1_Type_CRC32 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR5_EL1_Type_CRC32 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_ISAR5_EL1_Type_CRC32 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_ISAR5_Type_CRC32 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_AA64ISAR0_EL1_Type_FHM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)


def _update_ID_AA64ISAR0_EL1_Type_FHM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)


def _update_ID_ISAR6_EL1_Type_FHM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_ISAR6_EL1_Type_FHM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_ISAR6_Type_FHM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_AA64ISAR0_EL1_Type_RDM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_AA64ISAR0_EL1_Type_RDM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_ISAR5_EL1_Type_RDM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_ISAR5_EL1_Type_RDM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_ISAR5_Type_RDM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_AA64ISAR0_EL1_Type_RNDR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)


def _update_ID_AA64ISAR0_EL1_Type_RNDR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)


def _update_RNDR_Type_RNDR (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _get_RNDR_Type_RNDR (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_ID_AA64ISAR0_EL1_Type_SHA1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64ISAR0_EL1_Type_SHA1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR5_EL1_Type_SHA1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_ISAR5_EL1_Type_SHA1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_ISAR5_Type_SHA1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_AA64ISAR0_EL1_Type_SHA2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_AA64ISAR0_EL1_Type_SHA2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR5_EL1_Type_SHA2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_ISAR5_EL1_Type_SHA2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_ISAR5_Type_SHA2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_AA64ISAR0_EL1_Type_SHA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_ID_AA64ISAR0_EL1_Type_SHA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _update_ID_AA64ZFR0_EL1_Type_SHA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_ID_AA64ZFR0_EL1_Type_SHA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _get_ID_AA64ISAR0_EL1_Type_SM3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _update_ID_AA64ISAR0_EL1_Type_SM3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def _get_ID_AA64ISAR0_EL1_Type_SM4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _update_ID_AA64ISAR0_EL1_Type_SM4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _update_ID_AA64ZFR0_EL1_Type_SM4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _get_ID_AA64ZFR0_EL1_Type_SM4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _get_ID_AA64ISAR0_EL1_Type_TLB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)


def _update_ID_AA64ISAR0_EL1_Type_TLB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)


def Mk_PMMIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMMIR_EL1_Type_BUS_SLOTS (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _update_PMMIR_EL1_Type_BUS_SLOTS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _update_PMMIR_Type_BUS_SLOTS (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _get_PMMIR_Type_BUS_SLOTS (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_PMMIR_EL1_Type_BUS_WIDTH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_PMMIR_EL1_Type_BUS_WIDTH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_PMMIR_Type_BUS_WIDTH (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_PMMIR_Type_BUS_WIDTH (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_PMMIR_EL1_Type_EDGE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_PMMIR_EL1_Type_EDGE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_PMMIR_Type_EDGE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_PMMIR_Type_EDGE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_PMMIR_EL1_Type_SLOTS (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_PMMIR_EL1_Type_SLOTS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_PMMIR_Type_SLOTS (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_PMMIR_Type_SLOTS (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_PMMIR_EL1_Type_THWIDTH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_PMMIR_EL1_Type_THWIDTH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_PMMIR_Type_THWIDTH (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_PMMIR_Type_THWIDTH (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def Mk_ICV_IAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICC_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICC_HSRE_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICC_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_MSRE_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICC_SRE_EL2_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICC_SRE_EL3_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICV_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICV_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_ICC_HSRE_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICC_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_IGRPEN0_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_IGRPEN1_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_MSRE_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICC_SRE_EL2_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICC_SRE_EL3_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICV_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICV_IGRPEN0_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICV_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICV_IGRPEN1_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def Mk_ID_MMFR5_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_MMFR5_EL1_Type_ETS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_MMFR5_EL1_Type_ETS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_AA64MMFR1_EL1_Type_ETS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def _get_ID_AA64MMFR1_EL1_Type_ETS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _get_ID_MMFR5_Type_ETS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_MMFR5_EL1_Type_nTLBPA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_MMFR5_EL1_Type_nTLBPA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_AA64MMFR1_EL1_Type_nTLBPA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)


def _update_ID_MMFR5_Type_nTLBPA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_AA64MMFR1_EL1_Type_nTLBPA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)


def _get_ID_MMFR5_Type_nTLBPA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def Mk_ICC_NMIAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_DBGCLAIMSET_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGCLAIMSET_EL1_Type_CLAIM (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_DBGCLAIMSET_EL1_Type_CLAIM (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_DBGCLAIMCLR_EL1_Type_CLAIM (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_DBGCLAIMCLR_EL1_Type_CLAIM (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_DBGCLAIMCLR_Type_CLAIM (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_DBGCLAIMSET_Type_CLAIM (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICC_SRE_EL1_Type_DFB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_ICC_MSRE_Type_DFB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_SRE_EL2_Type_DFB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_SRE_EL3_Type_DFB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_ICC_HSRE_Type_DFB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_MSRE_Type_DFB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_SRE_EL2_Type_DFB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_SRE_EL3_Type_DFB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_SRE_Type_DFB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_SRE_EL1_Type_DIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_ICC_MSRE_Type_DIB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICC_SRE_EL2_Type_DIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICC_SRE_EL3_Type_DIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_ICC_HSRE_Type_DIB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_MSRE_Type_DIB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_SRE_EL2_Type_DIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_SRE_EL3_Type_DIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_SRE_Type_DIB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_SRE_EL1_Type_SRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICC_MSRE_Type_SRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_SRE_EL2_Type_SRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_SRE_EL3_Type_SRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_ICC_HSRE_Type_SRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_MSRE_Type_SRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_SRE_EL2_Type_SRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_SRE_EL3_Type_SRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_SRE_Type_SRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def undefined_ICH_AP0R_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ICH_AP0R_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_IAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_ISAR4_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_ISAR4_EL1_Type_Barrier (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_ISAR4_EL1_Type_Barrier (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_ISAR4_Type_Barrier (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_ISAR4_EL1_Type_PSR_M (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_ISAR4_EL1_Type_PSR_M (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_ISAR4_Type_PSR_M (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_ISAR4_EL1_Type_SMC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_ISAR4_EL1_Type_SMC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_ISAR4_Type_SMC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_ISAR4_EL1_Type_SWP_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_ISAR4_EL1_Type_SWP_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_ISAR4_Type_SWP_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_ISAR4_EL1_Type_SynchPrim_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_ISAR4_EL1_Type_SynchPrim_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_ISAR4_Type_SynchPrim_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_ISAR4_EL1_Type_Unpriv (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_ISAR4_EL1_Type_Unpriv (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_ISAR4_Type_Unpriv (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_ISAR4_EL1_Type_WithShifts (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_ISAR4_EL1_Type_WithShifts (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_ISAR4_Type_WithShifts (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_ISAR4_EL1_Type_Writeback (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_ISAR4_EL1_Type_Writeback (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_ISAR4_Type_Writeback (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def Mk_ID_ISAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_ISAR1_EL1_Type_Endian (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_ISAR1_EL1_Type_Endian (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_ISAR1_Type_Endian (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_ISAR1_EL1_Type_Except (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_ISAR1_EL1_Type_Except (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_ISAR1_Type_Except (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_ISAR1_EL1_Type_Except_AR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_ISAR1_EL1_Type_Except_AR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_ISAR1_Type_Except_AR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_ISAR1_EL1_Type_Extend (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_ISAR1_EL1_Type_Extend (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_ISAR1_Type_Extend (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_ISAR1_EL1_Type_IfThen (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_ISAR1_EL1_Type_IfThen (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_ISAR1_Type_IfThen (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_ISAR1_EL1_Type_Immediate (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_ISAR1_EL1_Type_Immediate (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


end ArmFull.Functions
