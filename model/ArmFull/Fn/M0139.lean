import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0063
import ArmFull.Fn.M0064
import ArmFull.Fn.M0065
import ArmFull.Fn.M0066
import ArmFull.Fn.M0067
import ArmFull.Fn.M0068
import ArmFull.Fn.M0069
import ArmFull.Fn.M0070
import ArmFull.Fn.M0071
import ArmFull.Fn.M0072
import ArmFull.Fn.M0073
import ArmFull.Fn.M0074
import ArmFull.Fn.M0075

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

def __get_HDFGRTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGRTR_EL2_Type := value_name
  (Mk_HDFGRTR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x1FE04C000300100#60 64)))))


def __get_ICV_NMIAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_NMIAR1_EL1_Type := value_name
  (Mk_ICV_NMIAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_SPSR_abt (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_abt_Type := value_name
  (Mk_SPSR_abt_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICH_LR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_LR_EL2_Type := value_name
  (Mk_ICH_LR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x700E00000000000#60 64)))))


def __get_MDCCINT_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCCINT_EL1_Type := value_name
  (Mk_MDCCINT_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF9FFFFFFF#64)))


def __get_ICC_HPPIR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_HPPIR1_EL1_Type := value_name
  (Mk_ICC_HPPIR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_TCR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR2_EL2_Type := value_name
  (Mk_TCR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_ESR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ESR_EL1_Type := value_name
  (Mk_ESR_EL1_Type (tmp &&& (Complement.complement 0xFFFFF88000000000#64)))


def __get_ICV_BPR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_BPR1_EL1_Type := value_name
  (Mk_ICV_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_TCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR_EL3_Type := value_name
  (Mk_TCR_EL3_Type
    ((tmp &&& (Complement.complement 0xFFFFF180000800C0#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x80800000#32 64))))


def __get_PMECR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMECR_EL1_Type := value_name
  (Mk_PMECR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))


def __get_ICC_PMR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_PMR_EL1_Type := value_name
  (Mk_ICC_PMR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))


def __get_RMR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RMR_EL1_Type := value_name
  (Mk_RMR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_PMICFILTR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMICFILTR_EL0_Type := value_name
  (Mk_PMICFILTR_EL0_Type (tmp &&& (Complement.complement 0xFBFFFFFF020F0000#64)))


def __get_ICC_HPPIR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_HPPIR0_EL1_Type := value_name
  (Mk_ICC_HPPIR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_CNTHPS_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHPS_CTL_EL2_Type := value_name
  (Mk_CNTHPS_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_VMECID_A_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VMECID_A_EL2_Type := value_name
  (Mk_VMECID_A_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_MECID_RL_A_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_RL_A_EL3_Type := value_name
  (Mk_MECID_RL_A_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_HSTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HSTR_EL2_Type := value_name
  (Mk_HSTR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF4010#64)))


def __get_PMOVSCLR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMOVSCLR_EL0_Type := value_name
  (Mk_PMOVSCLR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_HAFGRTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HAFGRTR_EL2_Type := value_name
  (Mk_HAFGRTR_EL2_Type (tmp &&& (Complement.complement 0xFFFC00000001FFE0#64)))


def __get_ICC_BPR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR0_EL1_Type := value_name
  (Mk_ICC_BPR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ACCDATA_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ACCDATA_EL1_Type := value_name
  (Mk_ACCDATA_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_PMSSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSSCR_EL1_Type := value_name
  (Mk_PMSSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFEFFFFFFFE#64)))


def __get_LORID_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORID_EL1_Type := value_name
  (Mk_LORID_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FF00#64)))


def __get_CONTEXTIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CONTEXTIDR_EL2_Type := value_name
  (Mk_CONTEXTIDR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_FPSR (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : FPSR_Type := value_name
  (Mk_FPSR_Type (tmp &&& (Complement.complement 0xFFFFFFFF07FFFF60#64)))


def __get_CNTP_TVAL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTP_TVAL_EL0_Type := value_name
  (Mk_CNTP_TVAL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ID_AA64MMFR4_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR4_EL1_Type := value_name
  (Mk_ID_AA64MMFR4_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF0F#64)))


def __get_ICH_EISR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_EISR_EL2_Type := value_name
  (Mk_ICH_EISR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_MIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MIDR_EL1_Type := value_name
  (Mk_MIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICC_RPR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_RPR_EL1_Type := value_name
  (Mk_ICC_RPR_EL1_Type (tmp &&& (Complement.complement 0x3FFFFFFFFFFFFF00#64)))


def __get_ICH_ELRSR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_ELRSR_EL2_Type := value_name
  (Mk_ICH_ELRSR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_HFGITR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGITR_EL2_Type := value_name
  (Mk_HFGITR_EL2_Type (tmp &&& (Complement.complement 0xE000000000000000#64)))


def __get_CNTHVS_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHVS_CTL_EL2_Type := value_name
  (Mk_CNTHVS_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ID_AA64PFR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64PFR1_EL1_Type := value_name
  (Mk_ID_AA64PFR1_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xF00000#24 64)))))


def __get_ICH_AP1R_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_AP1R_EL2_Type := value_name
  (Mk_ICH_AP1R_EL2_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))


def __get_SDER32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SDER32_EL2_Type := value_name
  (Mk_SDER32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_VSTCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VSTCR_EL2_Type := value_name
  (Mk_VSTCR_EL2_Type
    ((tmp &&& (Complement.complement 0xFFFFFFFD1FFF3F00#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x80000000#32 64))))


def __get_PMMIR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMMIR_EL1_Type := value_name
  (Mk_PMMIR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFF0000000#64)))


def __get_ICV_IAR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IAR0_EL1_Type := value_name
  (Mk_ICV_IAR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_ICC_IGRPEN1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL1_Type := value_name
  (Mk_ICC_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_ICC_IGRPEN1_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL1_Type := value_name
  (Mk_ICC_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_ICC_IGRPEN1_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL1_Type := value_name
  (Mk_ICC_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_GPTBR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GPTBR_EL3_Type := value_name
  (Mk_GPTBR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFF0000000000#64)))


def __get_MDCCSR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCCSR_EL0_Type := value_name
  (Mk_MDCCSR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF9FFFFFFF#64)))


def __get_TTBR0_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TTBR0_EL3_Type := value_name
  (Mk_TTBR0_EL3_Type (tmp &&& (Complement.complement 0xFF00000000000000#64)))


def __get_DBGBCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGBCR_EL1_Type := value_name
  (Mk_DBGBCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00001E10#64)))


def __get_PMCCFILTR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMCCFILTR_EL0_Type := value_name
  (Mk_PMCCFILTR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF020FFFFF#64)))


def __get_ICC_NMIAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_NMIAR1_EL1_Type := value_name
  (Mk_ICC_NMIAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_DBGCLAIMSET_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGCLAIMSET_EL1_Type := value_name
  (Mk_DBGCLAIMSET_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))


def __get_ICC_SRE_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL1_Type := value_name
  (Mk_ICC_SRE_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ICC_SRE_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL1_Type := value_name
  (Mk_ICC_SRE_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ICC_SRE_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL1_Type := value_name
  (Mk_ICC_SRE_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ICH_AP0R_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_AP0R_EL2_Type := value_name
  (Mk_ICH_AP0R_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICC_IAR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IAR0_EL1_Type := value_name
  (Mk_ICC_IAR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_ESR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ESR_EL2_Type := value_name
  (Mk_ESR_EL2_Type (tmp &&& (Complement.complement 0xFFFFF80000000000#64)))


def __get_CONTEXTIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CONTEXTIDR_EL1_Type := value_name
  (Mk_CONTEXTIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_PMUACR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMUACR_EL1_Type := value_name
  (Mk_PMUACR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_DSPSR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DSPSR_EL0_Type := value_name
  (Mk_DSPSR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))


def __get_RMR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RMR_EL2_Type := value_name
  (Mk_RMR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_VNCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VNCR_EL2_Type := value_name
  (Mk_VNCR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xFFF#12 64)))))


def __get_PMINTENCLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMINTENCLR_EL1_Type := value_name
  (Mk_PMINTENCLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_PMSELR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSELR_EL0_Type := value_name
  (Mk_PMSELR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))


def __get_ICC_CTLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL1_Type := value_name
  (Mk_ICC_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300BC#64)))


def __get_ICC_CTLR_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL1_Type := value_name
  (Mk_ICC_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300BC#64)))


def __get_ICC_CTLR_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL1_Type := value_name
  (Mk_ICC_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300BC#64)))


def __get_ICC_AP1R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP1R_EL1_Type := value_name
  (Mk_ICC_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))


def __get_ICC_AP1R_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP1R_EL1_Type := value_name
  (Mk_ICC_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))


def __get_ICC_AP1R_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP1R_EL1_Type := value_name
  (Mk_ICC_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))


def __get_CNTP_CTL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTP_CTL_EL0_Type := value_name
  (Mk_CNTP_CTL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_CNTHV_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHV_TVAL_EL2_Type := value_name
  (Mk_CNTHV_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_SPSR_irq (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_irq_Type := value_name
  (Mk_SPSR_irq_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICH_MISR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_MISR_EL2_Type := value_name
  (Mk_ICH_MISR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))


def __get_CSSELR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CSSELR_EL1_Type := value_name
  (Mk_CSSELR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))


def __get_ICV_RPR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_RPR_EL1_Type := value_name
  (Mk_ICV_RPR_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFFFFFFFF00#64)))


def __get_PFAR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PFAR_EL2_Type := value_name
  (Mk_PFAR_EL2_Type (tmp &&& (Complement.complement 0x3F00000000000000#64)))


def __get_ICV_PMR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_PMR_EL1_Type := value_name
  (Mk_ICV_PMR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))


def __get_MFAR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MFAR_EL3_Type := value_name
  (Mk_MFAR_EL3_Type (tmp &&& (Complement.complement 0x3F00000000000000#64)))


def __get_SPSR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_EL2_Type := value_name
  (Mk_SPSR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))


def __get_TCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR_EL1_Type := value_name
  (Mk_TCR_EL1_Type (tmp &&& (Complement.complement 0xC000000800000000#64)))


def __get_ICV_HPPIR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_HPPIR0_EL1_Type := value_name
  (Mk_ICV_HPPIR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_SCTLR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR2_EL1_Type := value_name
  (Mk_SCTLR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF83#64)))


def __get_ICV_BPR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_BPR0_EL1_Type := value_name
  (Mk_ICV_BPR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ISR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ISR_EL1_Type := value_name
  (Mk_ISR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF83F#64)))


def __get_MECIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECIDR_EL2_Type := value_name
  (Mk_MECIDR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_PMINTENSET_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMINTENSET_EL1_Type := value_name
  (Mk_PMINTENSET_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_SMIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMIDR_EL1_Type := value_name
  (Mk_SMIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00007000#64)))


def __get_HFGWTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGWTR_EL2_Type := value_name
  (Mk_HFGWTR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x845001624C604#52 64)))))


def __get_SMPRI_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMPRI_EL1_Type := value_name
  (Mk_SMPRI_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_PMUSERENR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMUSERENR_EL0_Type := value_name
  (Mk_PMUSERENR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF80#64)))


def __get_SCTLR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR2_EL2_Type := value_name
  (Mk_SCTLR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF81#64)))


def __get_PMOVSSET_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMOVSSET_EL0_Type := value_name
  (Mk_PMOVSSET_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_SCTLR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR_EL3_Type := value_name
  (Mk_SCTLR_EL3_Type
    ((tmp &&& (Complement.complement 0x97D7E4CF0512C780#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x30850030#32 64))))


def __get_ICV_CTLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_CTLR_EL1_Type := value_name
  (Mk_ICV_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300FC#64)))


def __get_MECID_A0_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_A0_EL2_Type := value_name
  (Mk_MECID_A0_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_ICV_IAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IAR1_EL1_Type := value_name
  (Mk_ICV_IAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_CPACR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CPACR_EL1_Type := value_name
  (Mk_CPACR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF4CCCFFFF#64)))


def __get_SPSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_EL1_Type := value_name
  (Mk_SPSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))


def __get_MDSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDSCR_EL1_Type := value_name
  (Mk_MDSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFF213100F82#64)))


def __get_SPSR_fiq (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_fiq_Type := value_name
  (Mk_SPSR_fiq_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_MECID_P0_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_P0_EL2_Type := value_name
  (Mk_MECID_P0_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_GPCCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GPCCR_EL3_Type := value_name
  (Mk_GPCCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF0C00F8#64)))


def __get_HDFGWTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGWTR2_EL2_Type := value_name
  (Mk_HDFGWTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFD60040#64)))


def __get_TCR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR2_EL1_Type := value_name
  (Mk_TCR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF33C0#64)))


def __get_DCZID_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DCZID_EL0_Type := value_name
  (Mk_DCZID_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))


def __get_VSTTBR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VSTTBR_EL2_Type := value_name
  (Mk_VSTTBR_EL2_Type (tmp &&& (Complement.complement 0xFF00000000000000#64)))


def __get_TRFCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TRFCR_EL2_Type := value_name
  (Mk_TRFCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF94#64)))


def __get_CNTHP_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHP_CTL_EL2_Type := value_name
  (Mk_CNTHP_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_CNTHVS_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHVS_TVAL_EL2_Type := value_name
  (Mk_CNTHVS_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_CNTHP_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHP_TVAL_EL2_Type := value_name
  (Mk_CNTHP_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_CNTHCTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHCTL_EL2_Type := value_name
  (Mk_CNTHCTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF00000#64)))


def __get_MDRAR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDRAR_EL1_Type := value_name
  (Mk_MDRAR_EL1_Type (tmp &&& (Complement.complement 0xFF00000000000FFC#64)))


def __get_PFAR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PFAR_EL1_Type := value_name
  (Mk_PFAR_EL1_Type (tmp &&& (Complement.complement 0x3F00000000000000#64)))


def __get_IFSR32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : IFSR32_EL2_Type := value_name
  (Mk_IFSR32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFEE9C0#64)))


def __get_ICC_IGRPEN1_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL3_Type := value_name
  (Mk_ICC_IGRPEN1_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_LORSA_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORSA_EL1_Type := value_name
  (Mk_LORSA_EL1_Type (tmp &&& (Complement.complement 0xFF0000000000FFFE#64)))


def __get_DBGWCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGWCR_EL1_Type := value_name
  (Mk_DBGWCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00E00000#64)))


def __get_ESR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ESR_EL3_Type := value_name
  (Mk_ESR_EL3_Type (tmp &&& (Complement.complement 0xFFFFF88000000000#64)))


def __get_PMEVTYPER_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMEVTYPER_EL0_Type := value_name
  (Mk_PMEVTYPER_EL0_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xBFFF000000F0000#60 64)))))


def __get_CNTV_CTL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTV_CTL_EL0_Type := value_name
  (Mk_CNTV_CTL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_TRFCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TRFCR_EL1_Type := value_name
  (Mk_TRFCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF9C#64)))


def __get_ICH_VMCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_VMCR_EL2_Type := value_name
  (Mk_ICH_VMCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF0003FDE0#64)))


def __get_VPIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VPIDR_EL2_Type := value_name
  (Mk_VPIDR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICC_CTLR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL3_Type := value_name
  (Mk_ICC_CTLR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF10080#64)))


def __get_SCTLR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR_EL2_Type := value_name
  (Mk_SCTLR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x400020200#36 64)))))


def __get_OSLSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSLSR_EL1_Type := value_name
  (Mk_OSLSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_MDCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCR_EL3_Type := value_name
  (Mk_MDCR_EL3_Type (tmp &&& (Complement.complement 0xFFFF80802740012A#64)))


def __get_SCTLR2_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR2_EL3_Type := value_name
  (Mk_SCTLR2_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE5#64)))


def __get_PMCNTENSET_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMCNTENSET_EL0_Type := value_name
  (Mk_PMCNTENSET_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_ICC_SRE_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL2_Type := value_name
  (Mk_ICC_SRE_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_CNTPS_CTL_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTPS_CTL_EL1_Type := value_name
  (Mk_CNTPS_CTL_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_DACR32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DACR32_EL2_Type := value_name
  (Mk_DACR32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_LORC_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORC_EL1_Type := value_name
  (Mk_LORC_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC02#64)))


def __get_ID_AA64PFR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64PFR2_EL1_Type := value_name
  (Mk_ID_AA64PFR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF000#64)))


def __get_TCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR_EL2_Type := value_name
  (Mk_TCR_EL2_Type (tmp &&& (Complement.complement 0xC000000800000040#64)))


def __get_CCSIDR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CCSIDR2_EL1_Type := value_name
  (Mk_CCSIDR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_CTR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CTR_EL0_Type := value_name
  (Mk_CTR_EL0_Type
    ((tmp &&& (Complement.complement 0xFFFFFFC040003FF0#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x80000000#32 64))))


def __get_SPSR_und (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_und_Type := value_name
  (Mk_SPSR_und_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ID_AA64ISAR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64ISAR2_EL1_Type := value_name
  (Mk_ID_AA64ISAR2_EL1_Type (tmp &&& (Complement.complement 0xFF00F00000000000#64)))


def __get_CPTR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CPTR_EL3_Type := value_name
  (Mk_CPTR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FEFEAFF#64)))


def __get_HFGRTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGRTR2_EL2_Type := value_name
  (Mk_HFGRTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_RMR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RMR_EL3_Type := value_name
  (Mk_RMR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_ICH_HCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_HCR_EL2_Type := value_name
  (Mk_ICH_HCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF07FF0200#64)))


def __get_ICC_IGRPEN0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN0_EL1_Type := value_name
  (Mk_ICC_IGRPEN0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


end ArmFull.Functions
