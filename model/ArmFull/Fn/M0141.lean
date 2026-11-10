import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0038
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0052
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0058
import ArmFull.Fn.M0063
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082

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

def __get_DBGVCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGVCR_Type := value_name
  (Mk_DBGVCR_Type (tmp &&& (Complement.complement 0x21FF2321#32)))


def __get_ICV_BPR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_BPR1_Type := value_name
  (Mk_ICV_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICC_RPR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_RPR_Type := value_name
  (Mk_ICC_RPR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_ICC_MSRE (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_MSRE_Type := value_name
  (Mk_ICC_MSRE_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))


def __get_PMMIR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMMIR_Type := value_name
  (Mk_PMMIR_Type (tmp &&& (Complement.complement 0xF0000000#32)))


def __get_VMPIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VMPIDR_Type := value_name
  (Mk_VMPIDR_Type ((tmp &&& (Complement.complement 0x3E000000#32)) ||| 0x80000000#32))


def __get_ICC_IGRPEN1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN1_Type := value_name
  (Mk_ICC_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_ICC_IGRPEN1_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN1_Type := value_name
  (Mk_ICC_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_ICC_IGRPEN1_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN1_Type := value_name
  (Mk_ICC_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_HSTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HSTR_Type := value_name
  (Mk_HSTR_Type (tmp &&& (Complement.complement 0xFFFF4010#32)))


def __get_ICC_MCTLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_MCTLR_Type := value_name
  (Mk_ICC_MCTLR_Type (tmp &&& (Complement.complement 0xFFF10080#32)))


def __get_PMSELR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMSELR_Type := value_name
  (Mk_PMSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))


def __get_DBGCLAIMSET (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGCLAIMSET_Type := value_name
  (Mk_DBGCLAIMSET_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_ICC_IGRPEN0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN0_Type := value_name
  (Mk_ICC_IGRPEN0_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_ICC_CTLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_CTLR_Type := value_name
  (Mk_ICC_CTLR_Type (tmp &&& (Complement.complement 0xFFF300BC#32)))


def __get_ICC_CTLR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_CTLR_Type := value_name
  (Mk_ICC_CTLR_Type (tmp &&& (Complement.complement 0xFFF300BC#32)))


def __get_ICC_CTLR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_CTLR_Type := value_name
  (Mk_ICC_CTLR_Type (tmp &&& (Complement.complement 0xFFF300BC#32)))


def __get_SCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : SCR_Type := value_name
  (Mk_SCR_Type (tmp &&& (Complement.complement 0xFFFF4C00#32)))


def __get_NSACR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : NSACR_Type := value_name
  (Mk_NSACR_Type (tmp &&& (Complement.complement 0xFFE873FF#32)))


def __get_ICV_BPR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_BPR0_Type := value_name
  (Mk_ICV_BPR0_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICH_EISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_EISR_Type := value_name
  (Mk_ICH_EISR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_HDCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HDCR_Type := value_name
  (Mk_HDCR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x3750000#28 32)))))


def __get_ICC_HSRE (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_HSRE_Type := value_name
  (Mk_ICC_HSRE_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))


def __get_PMCCFILTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMCCFILTR_Type := value_name
  (Mk_PMCCFILTR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x20FFFFF#28 32)))))


def __get_HTCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HTCR_Type := value_name
  (Mk_HTCR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x40#8 32)))))


def __get_ICC_PMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_PMR_Type := value_name
  (Mk_ICC_PMR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_ICH_HCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_HCR_Type := value_name
  (Mk_ICH_HCR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x7FF0200#28 32)))))


def __get_RMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : RMR_Type := value_name
  (Mk_RMR_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))


def __get_ICC_HPPIR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_HPPIR0_Type := value_name
  (Mk_ICC_HPPIR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_TTBCR2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TTBCR2_Type := value_name
  (Mk_TTBCR2_Type (tmp &&& (Complement.complement 0xC0000008#32)))


def __get_TTBCR2_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TTBCR2_Type := value_name
  (Mk_TTBCR2_Type (tmp &&& (Complement.complement 0xC0000008#32)))


def __get_TTBCR2_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TTBCR2_Type := value_name
  (Mk_TTBCR2_Type (tmp &&& (Complement.complement 0xC0000008#32)))


def __get_CNTKCTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTKCTL_Type := value_name
  (Mk_CNTKCTL_Type (tmp &&& (Complement.complement 0xFFFDFC00#32)))


def __get_ICV_PMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_PMR_Type := value_name
  (Mk_ICV_PMR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_ICV_HPPIR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_HPPIR0_Type := value_name
  (Mk_ICV_HPPIR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_DBGBCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGBCR_Type := value_name
  (Mk_DBGBCR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x1E10#16 32)))))


def __get_VTCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VTCR_Type := value_name
  (Mk_VTCR_Type
    ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x1900000#28 32))))) ||| 0x80000000#32))


def __get_ICC_MGRPEN1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_MGRPEN1_Type := value_name
  (Mk_ICC_MGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))


def __get_CCSIDR2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CCSIDR2_Type := value_name
  (Mk_CCSIDR2_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_ICH_MISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_MISR_Type := value_name
  (Mk_ICH_MISR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_ICV_IAR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IAR0_Type := value_name
  (Mk_ICV_IAR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_ISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ISR_Type := value_name
  (Mk_ISR_Type (tmp &&& (Complement.complement 0xFFFFF83F#32)))


def __get_DBGDSCRint (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDSCRint_Type := value_name
  (Mk_DBGDSCRint_Type (tmp &&& (Complement.complement 0x9FF86FC3#32)))


def __get_DBGDCCINT (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDCCINT_Type := value_name
  (Mk_DBGDCCINT_Type (tmp &&& (Complement.complement 0x9FFFFFFF#32)))


def __get_DBGDSCRext (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDSCRext_Type := value_name
  (Mk_DBGDSCRext_Type (tmp &&& (Complement.complement 0x13100F82#32)))


def __get_IFSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : IFSR_Type := value_name
  (Mk_IFSR_Type (tmp &&& (Complement.complement 0xFFFEE9C0#32)))


def __get_IFSR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : IFSR_Type := value_name
  (Mk_IFSR_Type (tmp &&& (Complement.complement 0xFFFEE9C0#32)))


def __get_IFSR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : IFSR_Type := value_name
  (Mk_IFSR_Type (tmp &&& (Complement.complement 0xFFFEE9C0#32)))


def __get_DBGDIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDIDR_Type := value_name
  (Mk_DBGDIDR_Type
    ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x2FFF#16 32))))) ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
        0x8000#16 32))))


def __get_CNTP_CTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTP_CTL_Type := value_name
  (Mk_CNTP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_CNTP_CTL_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTP_CTL_Type := value_name
  (Mk_CNTP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_CNTP_CTL_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTP_CTL_Type := value_name
  (Mk_CNTP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_HTRFCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HTRFCR_Type := value_name
  (Mk_HTRFCR_Type (tmp &&& (Complement.complement 0xFFFFFF94#32)))


def __get_PMEVTYPER (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMEVTYPER_Type := value_name
  (Mk_PMEVTYPER_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0xF0000#20 32)))))


def __get_CNTV_CTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTV_CTL_Type := value_name
  (Mk_CNTV_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_DBGOSLSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGOSLSR_Type := value_name
  (Mk_DBGOSLSR_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))


def __get_TRFCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TRFCR_Type := value_name
  (Mk_TRFCR_Type (tmp &&& (Complement.complement 0xFFFFFF9C#32)))


def __get_CNTHP_CTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTHP_CTL_Type := value_name
  (Mk_CNTHP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_MPIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : MPIDR_Type := value_name
  (Mk_MPIDR_Type ((tmp &&& (Complement.complement 0x3E000000#32)) ||| 0x80000000#32))


def __get_ICH_LRC (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_LRC_Type := value_name
  (Mk_ICH_LRC_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x700E000#28 32)))))


def __get_DSPSR2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DSPSR2_Type := value_name
  (Mk_DSPSR2_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICC_HPPIR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_HPPIR1_Type := value_name
  (Mk_ICC_HPPIR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_ICC_SRE (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_SRE_Type := value_name
  (Mk_ICC_SRE_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICC_SRE_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_SRE_Type := value_name
  (Mk_ICC_SRE_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICC_SRE_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_SRE_Type := value_name
  (Mk_ICC_SRE_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_SDCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : SDCR_Type := value_name
  (Mk_SDCR_Type (tmp &&& (Complement.complement 0xE7413FFF#32)))


def __get_AMEVTYPER0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMEVTYPER0_Type := value_name
  (Mk_AMEVTYPER0_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_AMUSERENR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMUSERENR_Type := value_name
  (Mk_AMUSERENR_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_AMEVTYPER1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMEVTYPER1_Type := value_name
  (Mk_AMEVTYPER1_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_AMCGCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCGCR_Type := value_name
  (Mk_AMCGCR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_AMCFGR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCFGR_Type := value_name
  (Mk_AMCFGR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0xEFFC000#28 32)))))


def __get_AMCNTENCLR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENCLR1_Type := value_name
  (Mk_AMCNTENCLR1_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_AMCNTENSET0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENSET0_Type := value_name
  (Mk_AMCNTENSET0_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))


def __get_AMCNTENCLR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENCLR0_Type := value_name
  (Mk_AMCNTENCLR0_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))


def __get_AMCNTENSET1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENSET1_Type := value_name
  (Mk_AMCNTENSET1_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_AMCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCR_Type := value_name
  (Mk_AMCR_Type (tmp &&& (Complement.complement 0xFFFDFBFF#32)))


def __get_ERRIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ERRIDR_Type := value_name
  (Mk_ERRIDR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_ERRSELR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ERRSELR_Type := value_name
  (Mk_ERRSELR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_DISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DISR_Type := value_name
  (Mk_DISR_Type (tmp &&& (Complement.complement 0x7E000000#32)))


def __get_VDFSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VDFSR_Type := value_name
  (Mk_VDFSR_Type (tmp &&& (Complement.complement 0xFE000000#32)))


def __get_VDISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VDISR_Type := value_name
  (Mk_VDISR_Type (tmp &&& (Complement.complement 0x7E000000#32)))


def __get_PAR_EL1 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : PAR_EL1_Type := value_name
  (Mk_PAR_EL1_Type (tmp &&& (Complement.complement 0xFF00000000000FFE0000000000000000#128)))


def __get_TTBR1_EL1 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR1_EL1_Type := value_name
  (Mk_TTBR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))


def __get_TTBR0_EL2 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR0_EL2_Type := value_name
  (Mk_TTBR0_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))


def __get_VTTBR_EL2 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : VTTBR_EL2_Type := value_name
  (Mk_VTTBR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))


def __get_TTBR0_EL1 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR0_EL1_Type := value_name
  (Mk_TTBR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))


def __get_TTBR1_EL2 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR1_EL2_Type := value_name
  (Mk_TTBR1_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))


/-- Type quantifiers: M : Nat, N : Nat, i : Int, M ≥ 0 ∧ N ≥ 0 -/
def ZeroUnsignedSatQ (i : Int) (N : Nat) (M : Nat) : SailM ((BitVec M) × Bool) := do
  let result ← (( do (undefined_int_at (← occLabel 2860) ()) ) : SailM Int )
  let saturated ← (( do (undefined_bool_at (← occLabel 2861) ()) ) : SailM Bool )
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i N) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i N) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b 0) : Bool)
        then
          (let result : Int := 0
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  let result : Int := result
  let fullresult : (BitVec M) := (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (M)))))
  let fullresult ← (( do
    if ((N >b 0) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b M)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:57129.54-57129.55"
        let fullresult : (BitVec M) :=
          (Sail.BitVec.updateSubrange fullresult (Sail.Int.toNatChecked ((N -i 1))) 0
            (Sail.BitVec.castWidth (integer_subrange result (N -i 1) 0)))
        (pure (fullresult)))
    else (pure (fullresult)) ) : SailM (BitVec M) )
  (pure ((fullresult, saturated)))


def CPYPostSizeChoice (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM (BitVec 64) := do
  let size : Int := (BitVec.toInt cpysize)
  let low : Int :=
    if ((size <b 0) : Bool)
    then size
    else 0
  let high : Nat :=
    if ((size <b 0) : Bool)
    then 0
    else (Sail.Int.toNatChecked (size))
  let selected ← (( do (undefined_range_at (← occLabel 2862) low high) ) : SailM Int )
  (pure ((integer_subrange selected 63 0)))


def CPYPreSizeChoice (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM (BitVec 64) := do
  let size : Int := (BitVec.toInt cpysize)
  let low : Int :=
    if ((size <b 0) : Bool)
    then size
    else 0
  let high : Nat :=
    if ((size <b 0) : Bool)
    then 0
    else (Sail.Int.toNatChecked (size))
  let selected ← (( do (undefined_range_at (← occLabel 2863) low high) ) : SailM Int )
  (pure ((integer_subrange selected 63 0)))


/-- Type quantifiers: N : Int, remaining : Int -/
def CPYSizeChoice (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) (remaining : Int) (N : Int) : SailM Int := do
  let limit : Int :=
    if ((remaining <b N) : Bool)
    then remaining
    else N
  ArmFull.assert (limit ≥b 1) "/home/doug/boss-scratch/armcert-defects/c27-accepted/armcert_c27.sail:377.21-377.22"
  (undefined_range_at (← occLabel 2864) 1 limit)


def MemCpyDirectionChoice (fromaddress : (BitVec 64)) (toaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Bool := do
  (__UNKNOWN_boolean ())


def MemCpyParametersIllformedE (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Bool := do
  (__UNKNOWN_boolean ())


def MemCpyParametersIllformedM (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Bool := do
  (__UNKNOWN_boolean ())


def MemCpyZeroSizeCheck (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: k_IsSETGE : Bool -/
def MemSetParametersIllformedE (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGE : Bool) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: k_IsSETGM : Bool -/
def MemSetParametersIllformedM (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGM : Bool) : SailM Bool := do
  (__UNKNOWN_boolean ())


def MemSetZeroSizeCheck (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: k_IsSETGE : Bool -/
def SETPostSizeChoice (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGE : Bool) : SailM (BitVec 64) := do
  let size : Int := (BitVec.toInt setsize)
  let alignment : Nat :=
    if (IsSETGE : Bool)
    then 16
    else 1
  let magnitude : Nat :=
    if ((size <b 0) : Bool)
    then (Sail.Int.toNatChecked ((Neg.neg size)))
    else (Sail.Int.toNatChecked (size))
  let units : Int := (Int.ediv magnitude alignment)
  let selected ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 2865) 0 units))) ) :
    SailM Nat )
  let amount : Int := (selected *i alignment)
  let result : Int :=
    if ((size <b 0) : Bool)
    then (Neg.neg amount)
    else amount
  (pure ((integer_subrange result 63 0)))


/-- Type quantifiers: k_IsSETGP : Bool -/
def SETPreSizeChoice (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGP : Bool) : SailM (BitVec 64) := do
  let size : Int := (BitVec.toInt setsize)
  let alignment : Nat :=
    if (IsSETGP : Bool)
    then 16
    else 1
  let magnitude : Nat :=
    if ((size <b 0) : Bool)
    then (Sail.Int.toNatChecked ((Neg.neg size)))
    else (Sail.Int.toNatChecked (size))
  let units : Int := (Int.ediv magnitude alignment)
  let selected ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 2866) 0 units))) ) :
    SailM Nat )
  let amount : Int := (selected *i alignment)
  let result : Int :=
    if ((size <b 0) : Bool)
    then (Neg.neg amount)
    else amount
  (pure ((integer_subrange result 63 0)))


/-- Type quantifiers: AlignSize : Int, remaining : Int -/
def SETSizeChoice (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (AlignSize : Int) (remaining : Int) : SailM Int := do
  ArmFull.assert ((AlignSize == 1) || (AlignSize == 16)) "/home/doug/boss-scratch/armcert-defects/c27-accepted/armcert_c27.sail:386.43-386.44"
  let units : Int := (fdiv_int remaining AlignSize)
  ArmFull.assert (units ≥b 1) "/home/doug/boss-scratch/armcert-defects/c27-accepted/armcert_c27.sail:388.21-388.22"
  let selected ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 2867) 1 units))) ) :
    SailM Nat )
  (pure ((selected *i AlignSize)))


def undefined_DxB (ℓ : ChoiceLabel) (_ : Unit) : SailM DxB := do
  let w__0 ← (( do (undefined_MBReqDomain (ℓ.child 0) ()) ) : SailM MBReqDomain )
  let w__1 ← (( do (undefined_MBReqTypes (ℓ.child 1) ()) ) : SailM MBReqTypes )
  let w__2 ← (( do (undefined_bool_at (ℓ.child 2) ()) ) : SailM Bool )
  (pure ({ domain := w__0
           types := w__1
           nXS := w__2 }))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_0efd385ac3f50aa7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_32a7e4332477435d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_48d575ae64c47181 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_6fb8f8a119c2917d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_8025c4d237ad3c30 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF0_EL2_SysRegRead_906fb8ee06808f75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  sailThrow ((Error_Undefined ()))


end ArmFull.Functions
