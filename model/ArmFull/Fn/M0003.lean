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

def _update_ICV_RPR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ICV_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_AA64DFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64DFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64ISAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64ISAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64ISAR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64MMFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64MMFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64MMFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64MMFR3_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64MMFR4_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64PFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64PFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64PFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64SMFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_AA64ZFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_DFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_DFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_DFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_DFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR3_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR4_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR5_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR5_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_ISAR6_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_ISAR6_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_MMFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_MMFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_MMFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_MMFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_MMFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_MMFR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_MMFR3_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_MMFR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_MMFR4_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_MMFR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_MMFR5_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_MMFR5_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_PFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_PFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_PFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_PFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ID_PFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ID_PFR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_IFSR32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_IFSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ISR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_LORC_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_LOREA_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_LORID_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_LORN_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_LORSA_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MAIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MAIR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIR2_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MAIR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDCCINT_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDCCSR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDRAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MDSELR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MECIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MECID_A0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MECID_A1_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MECID_P0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MECID_P1_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MECID_RL_A_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MFAR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MPAM0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAM1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAM2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAM3_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMHCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMSM_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM1_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM3_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM4_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM5_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM6_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPM7_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPAMVPMV_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MVBAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MVFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MVFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MVFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MVFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_MVFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_MVFR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_NMRR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_NSACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_OSDLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_OSECCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_OSLAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_OSLSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PAR_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((128 -i 1))) 0 x)


def _update_PAR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PFAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PFAR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PIRE0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PIRE0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PIR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PIR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMAUTHSTATUS_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMBIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMBLIMITR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMBPTR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMBSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCCFILTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCCFILTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCCNTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCCNTR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCCNTSVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCEID0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCEID0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCEID1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCEID1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCEID2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCEID3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCFGR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCGCR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCNTENCLR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCNTENCLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCNTENSET_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCNTENSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMCNTEN_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMECR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMEVCNTSVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMEVTYPER_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMEVTYPER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMIAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMICFILTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMICNTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMICNTSVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMIIDR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMINTENCLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMINTENCLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMINTENSET_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMINTENSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMINTEN_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMITCTRL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMLAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMLSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMMIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMMIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMOVSCLR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMOVSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMOVSSET_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMOVSSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMOVS_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMPCSCTL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMPCSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSDSFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSELR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSELR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_PMSEVFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSFCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSICR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSIRR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_PMSLATFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


end ArmFull.Functions
