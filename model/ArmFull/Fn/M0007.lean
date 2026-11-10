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

def _get_LOREA_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_LORID_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_LORN_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_LORSA_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MAIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MAIR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIR2_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MAIR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDCCINT_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDCCSR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDRAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDSCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MDSELR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MECIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MECID_A0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MECID_A1_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MECID_P0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MECID_P1_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MECID_RL_A_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MFAR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MPAM0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAM1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAM2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAM3_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMHCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMSM_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM1_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM3_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM4_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM5_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM6_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPM7_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPAMVPMV_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MVBAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MVFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MVFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MVFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MVFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_MVFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_MVFR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_NMRR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_NSACR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_OSDLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_OSECCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_OSLAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_OSLSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PAR_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_PAR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PFAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PFAR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PIRE0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PIRE0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PIR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PIR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMAUTHSTATUS_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMBIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMBLIMITR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMBPTR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMBSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCCFILTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCCFILTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCCNTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCCNTR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCCNTSVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCEID0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCEID0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCEID1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCEID1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCEID2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCEID3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCFGR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCGCR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCNTENCLR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCNTENCLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCNTENSET_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCNTENSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMCNTEN_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMDEVID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMDEVTYPE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMECR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMEVCNTSVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMEVTYPER_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMEVTYPER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMIAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMICFILTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMICNTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMICNTSVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMIIDR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMINTENCLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMINTENCLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMINTENSET_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMINTENSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMINTEN_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMITCTRL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMLAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMLSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMMIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMMIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMOVSCLR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMOVSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMOVSSET_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMOVSSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMOVS_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMPCSCTL_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMPCSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMPIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMPIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMPIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMPIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMPIDR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMSCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSDSFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSELR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSELR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMSEVFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSFCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSICR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSIRR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSLATFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSNEVFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSSCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSWINC_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMSWINC_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMUACR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMUSERENR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMUSERENR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMVCIDSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMVIDSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_PMXEVCNTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PMZR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_POR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_POR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_POR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_POR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_PRRR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_RCWMASK_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_RCWSMASK_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_RGSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RMR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RMR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RMR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_RNDRRS_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RNDR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RVBAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RVBAR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_RVBAR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_S1PIRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_S1PORType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_S2PIRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_S2PIR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_S2POR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SCTLR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLR2_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SCTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SDCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SDER32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SDER32_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SDER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SMCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SMCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SMCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SMIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SMPRIMAP_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SMPRI_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPMACCESSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPMACCESSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPMACCESSR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPMSELR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


end ArmFull.Functions
