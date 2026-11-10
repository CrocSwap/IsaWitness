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

def _update_MDCR_EL3_Type_NSPBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_MDCR_EL3_Type_RLTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_MDCR_EL3_Type_RLTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_MDCR_EL3_Type_SBRBE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)


def _update_MDCR_EL3_Type_SBRBE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)


def _get_MDCR_EL3_Type_SCCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _update_MDCR_EL3_Type_SCCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_SDCR_Type_SCCD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _get_SDCR_Type_SCCD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_MDCR_EL3_Type_SPD32 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_MDCR_EL3_Type_SPD32 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_MDCR_EL3_Type_SPME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_MDCR_EL3_Type_SPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_SDCR_Type_SPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_SDCR_Type_SPME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_MDCR_EL3_Type_STE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_MDCR_EL3_Type_STE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_SDCR_Type_STE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_SDCR_Type_STE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def undefined_PMCCFILTR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMCCFILTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMCCFILTR_EL0_Type_NSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_PMCCFILTR_EL0_Type_NSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_PMCCFILTR_Type_NSH (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_PMEVTYPER_EL0_Type_NSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_PMEVTYPER_Type_NSH (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_PMICFILTR_EL0_Type_NSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_PMCCFILTR_Type_NSH (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_PMEVTYPER_EL0_Type_NSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_PMEVTYPER_Type_NSH (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_PMICFILTR_EL0_Type_NSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_PMCCFILTR_EL0_Type_NSK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_PMCCFILTR_EL0_Type_NSK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_PMCCFILTR_Type_NSK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_PMEVTYPER_EL0_Type_NSK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_PMEVTYPER_Type_NSK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_PMICFILTR_EL0_Type_NSK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_PMCCFILTR_Type_NSK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_PMEVTYPER_EL0_Type_NSK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_PMEVTYPER_Type_NSK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_PMICFILTR_EL0_Type_NSK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_PMCCFILTR_EL0_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_PMCCFILTR_EL0_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_DBGVCR32_EL2_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_DBGVCR_Type_NSU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_PMCCFILTR_Type_NSU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_PMEVTYPER_EL0_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_PMEVTYPER_Type_NSU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_PMICFILTR_EL0_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_DBGVCR32_EL2_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_DBGVCR_Type_NSU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_PMCCFILTR_Type_NSU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_PMEVTYPER_EL0_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_PMEVTYPER_Type_NSU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_PMICFILTR_EL0_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_PMCCFILTR_EL0_Type_RLH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_PMCCFILTR_EL0_Type_RLH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_PMEVTYPER_EL0_Type_RLH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_PMICFILTR_EL0_Type_RLH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_PMEVTYPER_EL0_Type_RLH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_PMICFILTR_EL0_Type_RLH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_PMCCFILTR_EL0_Type_RLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_PMCCFILTR_EL0_Type_RLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_PMEVTYPER_EL0_Type_RLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_PMICFILTR_EL0_Type_RLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_PMEVTYPER_EL0_Type_RLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_PMICFILTR_EL0_Type_RLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_PMCCFILTR_EL0_Type_RLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_PMCCFILTR_EL0_Type_RLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_PMCCFILTR_Type_RLU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_PMEVTYPER_EL0_Type_RLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_PMEVTYPER_Type_RLU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_PMICFILTR_EL0_Type_RLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_PMCCFILTR_Type_RLU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_PMEVTYPER_EL0_Type_RLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_PMEVTYPER_Type_RLU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_PMICFILTR_EL0_Type_RLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_PMCCFILTR_EL0_Type_SH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_PMCCFILTR_EL0_Type_SH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_GPCCR_EL3_Type_SH (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_PAR_EL1_Type_SH (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 8 7 x)


def _update_PAR_Type_SH (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 7 x)


def _update_PMEVTYPER_EL0_Type_SH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_PMICFILTR_EL0_Type_SH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_GPCCR_EL3_Type_SH (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_PAR_EL1_Type_SH (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)


def _get_PAR_Type_SH (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)


def _get_PMEVTYPER_EL0_Type_SH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_PMICFILTR_EL0_Type_SH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_PMCCFILTR_EL0_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_PMCCFILTR_EL0_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_DBGVCR32_EL2_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_DBGVCR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICH_MISR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICH_MISR_EL2_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICH_MISR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_MPIDR_EL1_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_MPIDR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_PMCCFILTR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_PMEVTYPER_EL0_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_PMEVTYPER_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_PMICFILTR_EL0_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_VMPIDR_EL2_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_VMPIDR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_DBGVCR32_EL2_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_DBGVCR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_GICH_MISR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICH_MISR_EL2_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICH_MISR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_MPIDR_EL1_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_MPIDR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_PMCCFILTR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_PMEVTYPER_EL0_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_PMEVTYPER_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_PMICFILTR_EL0_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_VMPIDR_EL2_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_VMPIDR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def undefined_PMCCFILTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_PMCCFILTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def PMCCFILTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCCFILTR ) : SailM PMCCFILTR_Type )
  let w__0 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_PMCNTENSET_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMCNTENSET_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PMCNTENSET_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_PMCNTENSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def PMCNTENSET_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCNTENSET ) : SailM PMCNTENSET_Type )
  let w__0 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_PMEVTYPER_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMEVTYPER_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMEVTYPER_EL0_Type_MT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_PMEVTYPER_EL0_Type_MT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_MPIDR_EL1_Type_MT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_MPIDR_Type_MT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_PMEVTYPER_Type_MT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_VMPIDR_EL2_Type_MT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_VMPIDR_Type_MT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_MPIDR_EL1_Type_MT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_MPIDR_Type_MT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_PMEVTYPER_Type_MT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_VMPIDR_EL2_Type_MT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_VMPIDR_Type_MT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_PMEVTYPER_EL0_Type_SYNC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_PMEVTYPER_EL0_Type_SYNC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _update_PMICFILTR_EL0_Type_SYNC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _get_PMICFILTR_EL0_Type_SYNC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _get_PMEVTYPER_EL0_Type_TC (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 63 61)


def _update_PMEVTYPER_EL0_Type_TC (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 61 x)


def _update_ICH_HCR_EL2_Type_TC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_ICH_HCR_Type_TC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_ICH_HCR_EL2_Type_TC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_ICH_HCR_Type_TC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_PMEVTYPER_EL0_Type_TE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_PMEVTYPER_EL0_Type_TE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_HSCTLR_Type_TE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SCTLR_Type_TE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_HSCTLR_Type_TE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SCTLR_Type_TE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_PMEVTYPER_EL0_Type_TH (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 43 32)


def _update_PMEVTYPER_EL0_Type_TH (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 32 x)


def _get_PMEVTYPER_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 9 0))


def _update_PMEVTYPER_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 9 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((15 -i 10) +i 1)) -i ((9 -i 0) +i 1)) +i 1)))))


def _update_AMEVTYPER0_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_AMEVTYPER0_Type_evtCount (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_AMEVTYPER1_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_AMEVTYPER1_Type_evtCount (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_PMEVTYPER_Type_evtCount (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 9 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((15 -i 10) +i 1)) -i ((9 -i 0) +i 1)) +i 1)))))


def _update_PMICFILTR_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_AMEVTYPER0_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_AMEVTYPER0_Type_evtCount (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_AMEVTYPER1_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_AMEVTYPER1_Type_evtCount (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_PMEVTYPER_Type_evtCount (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 9 0))


def _get_PMICFILTR_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def undefined_PMEVTYPER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_PMEVTYPER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 31 -/
def PMEVTYPER_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _PMEVTYPER ) : SailM (Vector (BitVec 32) 31) )
  let r : PMEVTYPER_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


def undefined_PMICFILTR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMICFILTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SDCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_SDCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_SDCR_Type_SPD (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_SDCR_Type_SPD (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_EDPRSR_Type_SPD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_EDPRSR_Type_SPD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def undefined_SDER32_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SDER32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SDER32_EL2_Type_SUIDEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_SDER32_EL2_Type_SUIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_SDER32_EL3_Type_SUIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_SDER_Type_SUIDEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_SDER32_EL3_Type_SUIDEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_SDER_Type_SUIDEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_SDER32_EL2_Type_SUNIDEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_SDER32_EL2_Type_SUNIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_SDER32_EL3_Type_SUNIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


end ArmFull.Functions
