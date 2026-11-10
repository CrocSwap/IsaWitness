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

def _get_GICV_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GICV_EOIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GICV_HPPIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GICV_IAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GICV_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GICV_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GICV_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_CBASER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GITS_CREADR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GITS_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_CWRITER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GITS_IIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_MPAMIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_MPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_PARTIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_SGIR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GITS_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_GITS_TYPER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GMID_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GPCCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_GPTBR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HAFGRTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HCPTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HCR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HCRX_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HDCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HDFGRTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HDFGRTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HDFGWTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HDFGWTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HFGITR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HFGRTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HFGRTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HFGWTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HFGWTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HMAIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HMAIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HPFAR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HPFAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HRMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HSCTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HSTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_HSTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HTCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HTRFCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_HTTBR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_AP1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_ASGI1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_ASGI1R_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_BPR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_BPR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_BPR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_BPR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_CTLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_CTLR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_DIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_EOIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_EOIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_EOIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_EOIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_HPPIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_HPPIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_HPPIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_HPPIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_HSRE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_IAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_IAR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_IAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_IAR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_IGRPEN0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_IGRPEN1_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_IGRPEN1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_MCTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_MGRPEN1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_MSRE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_NMIAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_PMR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_RPR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICC_SGI0R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SGI0R_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SGI1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SGI1R_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SRE_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SRE_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SRE_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICC_SRE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_AP0R_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_AP0R_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_AP1R_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_AP1R_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_EISR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_EISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_ELRSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_ELRSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_HCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_HCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_LRC_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_LR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_LR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_MISR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_MISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_VMCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_VMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICH_VTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICH_VTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_AP1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_BPR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_BPR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_BPR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_BPR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_CTLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_DIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_EOIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_EOIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_EOIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_EOIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_HPPIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_HPPIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_HPPIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_HPPIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_IAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_IAR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_IAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_IAR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_IGRPEN0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_IGRPEN1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_NMIAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_PMR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ICV_RPR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ICV_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_AA64DFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64DFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64ISAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64ISAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64ISAR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64MMFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64MMFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64MMFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64MMFR3_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64MMFR4_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64PFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64PFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64PFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64SMFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_AA64ZFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_DFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_DFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_DFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_DFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR3_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR4_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR5_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR5_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_ISAR6_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_ISAR6_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_MMFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_MMFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_MMFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_MMFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_MMFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_MMFR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_MMFR3_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_MMFR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_MMFR4_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_MMFR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_MMFR5_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_MMFR5_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_PFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_PFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_PFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_PFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ID_PFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ID_PFR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_IFSR32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_IFSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_ISR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_LORC_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


end ArmFull.Functions
