import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0052
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0063
import ArmFull.Fn.M0069
import ArmFull.Fn.M0075
import ArmFull.Fn.M0076
import ArmFull.Fn.M0077
import ArmFull.Fn.M0079
import ArmFull.Fn.M0080
import ArmFull.Fn.M0081

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

def __get_CNTHPS_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHPS_TVAL_EL2_Type := value_name
  (Mk_CNTHPS_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICC_BPR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR1_EL1_Type := value_name
  (Mk_ICC_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ICC_BPR1_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR1_EL1_Type := value_name
  (Mk_ICC_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ICC_BPR1_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR1_EL1_Type := value_name
  (Mk_ICC_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_MECID_A1_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_A1_EL2_Type := value_name
  (Mk_MECID_A1_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_ID_AA64MMFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR0_EL1_Type := value_name
  (Mk_ID_AA64MMFR0_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xFF000000000000#56 64)))))


def __get_HDFGRTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGRTR2_EL2_Type := value_name
  (Mk_HDFGRTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF00000#64)))


def __get_DBGPRCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGPRCR_EL1_Type := value_name
  (Mk_DBGPRCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_PMCNTENCLR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMCNTENCLR_EL0_Type := value_name
  (Mk_PMCNTENCLR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))


def __get_SDER32_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SDER32_EL3_Type := value_name
  (Mk_SDER32_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_HPFAR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HPFAR_EL2_Type := value_name
  (Mk_HPFAR_EL2_Type (tmp &&& (Complement.complement 0x7FFF00000000000F#64)))


def __get_VMPIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VMPIDR_EL2_Type := value_name
  (Mk_VMPIDR_EL2_Type
    ((tmp &&& (Complement.complement 0xFFFFFF003E000000#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x80000000#32 64))))


def __get_ID_AA64MMFR3_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR3_EL1_Type := value_name
  (Mk_ID_AA64MMFR3_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xF000000000000#52 64)))))


def __get_ICH_VTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_VTR_EL2_Type := value_name
  (Mk_ICH_VTR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF0003FFE0#64)))


def __get_MDSELR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDSELR_EL1_Type := value_name
  (Mk_MDSELR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFCF#64)))


def __get_MDCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCR_EL2_Type := value_name
  (Mk_MDCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFF4EF03750000#64)))


def __get_CNTKCTL_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTKCTL_EL1_Type := value_name
  (Mk_CNTKCTL_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFDFC00#64)))


def __get_LORN_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORN_EL1_Type := value_name
  (Mk_LORN_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))


def __get_ICV_IGRPEN0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IGRPEN0_EL1_Type := value_name
  (Mk_ICV_IGRPEN0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_SPSR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_EL3_Type := value_name
  (Mk_SPSR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))


def __get_CCSIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CCSIDR_EL1_Type := value_name
  (Mk_CCSIDR_EL1_Type (tmp &&& (Complement.complement 0xFF00000000000000#64)))


def __get_VMECID_P_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VMECID_P_EL2_Type := value_name
  (Mk_VMECID_P_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_OSECCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSECCR_EL1_Type := value_name
  (Mk_OSECCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_DBGVCR32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGVCR32_EL2_Type := value_name
  (Mk_DBGVCR32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF21FF2321#64)))


def __get_HFGRTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGRTR_EL2_Type := value_name
  (Mk_HFGRTR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x8000000000000#52 64)))))


def __get_CPTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CPTR_EL2_Type := value_name
  (Mk_CPTR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF0CCC4000#64)))


def __get_CLIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CLIDR_EL1_Type := value_name
  (Mk_CLIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFF800000000000#64)))


def __get_HCRX_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HCRX_EL2_Type := value_name
  (Mk_HCRX_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF803000#64)))


def __get_ICV_IGRPEN1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IGRPEN1_EL1_Type := value_name
  (Mk_ICV_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_HFGWTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGWTR2_EL2_Type := value_name
  (Mk_HFGWTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFA#64)))


def __get_MECID_P1_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_P1_EL2_Type := value_name
  (Mk_MECID_P1_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_SPMSELR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPMSELR_EL0_Type := value_name
  (Mk_SPMSELR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC0C#64)))


def __get_DBGAUTHSTATUS_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGAUTHSTATUS_EL1_Type := value_name
  (Mk_DBGAUTHSTATUS_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFF0FF0F00#64)))


def __get_ICC_SRE_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL3_Type := value_name
  (Mk_ICC_SRE_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_HDFGWTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGWTR_EL2_Type := value_name
  (Mk_HDFGWTR_EL2_Type (tmp &&& (Complement.complement 0x8DFC89C440400240#64)))


def __get_CNTPS_TVAL_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTPS_TVAL_EL1_Type := value_name
  (Mk_CNTPS_TVAL_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICV_AP1R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_AP1R_EL1_Type := value_name
  (Mk_ICV_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))


def __get_LOREA_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LOREA_EL1_Type := value_name
  (Mk_LOREA_EL1_Type (tmp &&& (Complement.complement 0xFF0000000000FFFF#64)))


def __get_CNTV_TVAL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTV_TVAL_EL0_Type := value_name
  (Mk_CNTV_TVAL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_ICC_IAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IAR1_EL1_Type := value_name
  (Mk_ICC_IAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_MPIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPIDR_EL1_Type := value_name
  (Mk_MPIDR_EL1_Type
    ((tmp &&& (Complement.complement 0xFFFFFF003E000000#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x80000000#32 64))))


def __get_DBGCLAIMCLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGCLAIMCLR_EL1_Type := value_name
  (Mk_DBGCLAIMCLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))


def __get_DBGWVR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGWVR_EL1_Type := value_name
  (Mk_DBGWVR_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x3#4 64)))))


def __get_ICV_HPPIR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_HPPIR1_EL1_Type := value_name
  (Mk_ICV_HPPIR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))


def __get_CNTHV_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHV_CTL_EL2_Type := value_name
  (Mk_CNTHV_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))


def __get_ID_AA64ZFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64ZFR0_EL1_Type := value_name
  (Mk_ID_AA64ZFR0_EL1_Type (tmp &&& (Complement.complement 0xF00F00F0F000FF00#64)))


def __get_DBGDRAR (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGDRAR_Type := value_name
  (Mk_DBGDRAR_Type (tmp &&& (Complement.complement 0xFF00000000000FFC#64)))


def __get_ZCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ZCR_EL3_Type := value_name
  (Mk_ZCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_ZCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ZCR_EL1_Type := value_name
  (Mk_ZCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_ZCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ZCR_EL2_Type := value_name
  (Mk_ZCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_SMCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMCR_EL3_Type := value_name
  (Mk_SMCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FFFFFF0#64)))


def __get_SMCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMCR_EL1_Type := value_name
  (Mk_SMCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FFFFFF0#64)))


def __get_SMCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMCR_EL2_Type := value_name
  (Mk_SMCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FFFFFF0#64)))


def __get_ID_AA64SMFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64SMFR0_EL1_Type := value_name
  (Mk_ID_AA64SMFR0_EL1_Type (tmp &&& (Complement.complement 0x700E0300FFFFFFFF#64)))


def __get_MPAMHCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAMHCR_EL2_Type := value_name
  (Mk_MPAMHCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF7FFFFEFC#64)))


def __get_MPAMIDR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : MPAMIDR_EL1_Type := value_name
  let tmp : MPAMIDR_EL1_Type :=
    (Mk_MPAMIDR_EL1_Type (tmp &&& (Complement.complement 0xC1FFFF00FFE10000#64)))
  let w__0 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let tmp : (BitVec 64) :=
    if ((! ((_get_MPAMIDR_EL1_Type_HAS_HCR w__0) == 1#1)) : Bool)
    then
      (Mk_MPAMIDR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1C0000#24 64)))))
    else tmp
  (pure (tmp))


def __get_MPAM2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM2_EL2_Type := value_name
  (Mk_MPAM2_EL2_Type (tmp &&& (Complement.complement 0x7A38000000000000#64)))


def __get_MPAM3_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM3_EL3_Type := value_name
  (Mk_MPAM3_EL3_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xC6F000000000000#60 64)))))


def __get_MPAM0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM0_EL1_Type := value_name
  (Mk_MPAM0_EL1_Type (tmp &&& (Complement.complement 0xFFFF000000000000#64)))


def __get_MPAMSM_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAMSM_EL1_Type := value_name
  (Mk_MPAMSM_EL1_Type (tmp &&& (Complement.complement 0xFFFF00FF0000FFFF#64)))


def __get_MPAM1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM1_EL1_Type := value_name
  (Mk_MPAM1_EL1_Type (tmp &&& (Complement.complement 0x6FBF000000000000#64)))


def __get_MPAMVPMV_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAMVPMV_EL2_Type := value_name
  (Mk_MPAMVPMV_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_GMID_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GMID_EL1_Type := value_name
  (Mk_GMID_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_TFSR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSR_EL3_Type := value_name
  (Mk_TFSR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_TFSRE0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSRE0_EL1_Type := value_name
  (Mk_TFSRE0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_TFSR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSR_EL2_Type := value_name
  (Mk_TFSR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_TFSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSR_EL1_Type := value_name
  (Mk_TFSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))


def __get_RGSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RGSR_EL1_Type := value_name
  (Mk_RGSR_EL1_Type (tmp &&& (Complement.complement 0xFF000000000000F0#64)))


def __get_GCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCR_EL1_Type := value_name
  (Mk_GCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFE0000#64)))


def __get_AMCR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCR_EL0_Type := value_name
  (Mk_AMCR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFDFBFF#64)))


def __get_AMCNTENSET0_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENSET0_EL0_Type := value_name
  (Mk_AMCNTENSET0_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_AMCNTENCLR0_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENCLR0_EL0_Type := value_name
  (Mk_AMCNTENCLR0_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))


def __get_AMEVTYPER0_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMEVTYPER0_EL0_Type := value_name
  (Mk_AMEVTYPER0_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_AMCNTENSET1_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENSET1_EL0_Type := value_name
  (Mk_AMCNTENSET1_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_AMCNTENCLR1_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENCLR1_EL0_Type := value_name
  (Mk_AMCNTENCLR1_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_AMCFGR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCFGR_EL0_Type := value_name
  (Mk_AMCFGR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF0EFFC000#64)))


def __get_AMUSERENR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMUSERENR_EL0_Type := value_name
  (Mk_AMUSERENR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))


def __get_AMCG1IDR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCG1IDR_EL0_Type := value_name
  (Mk_AMCG1IDR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))


def __get_AMEVTYPER1_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMEVTYPER1_EL0_Type := value_name
  (Mk_AMEVTYPER1_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_AMCGCR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCGCR_EL0_Type := value_name
  (Mk_AMCGCR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_PMSFCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSFCR_EL1_Type := value_name
  (Mk_PMSFCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF8FFE0#64)))


def __get_PMSIRR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSIRR_EL1_Type := value_name
  (Mk_PMSIRR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF000000FE#64)))


def __get_PMSICR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSICR_EL1_Type := value_name
  (Mk_PMSICR_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xFFFFFF00000000#56 64)))))


def __get_PMBLIMITR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMBLIMITR_EL1_Type := value_name
  (Mk_PMBLIMITR_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xFD8#12 64)))))


def __get_PMBSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMBSR_EL1_Type := value_name
  (Mk_PMBSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFF1F03F00000#64)))


def __get_PMSCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSCR_EL2_Type := value_name
  (Mk_PMSCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF04#64)))


def __get_PMSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSCR_EL1_Type := value_name
  (Mk_PMSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF04#64)))


def __get_PMSIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSIDR_EL1_Type := value_name
  (Mk_PMSIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFC000000#64)))


def __get_PMBIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMBIDR_EL1_Type := value_name
  (Mk_PMBIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF0C0#64)))


def __get_PMSLATFR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSLATFR_EL1_Type := value_name
  (Mk_PMSLATFR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_VDISR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VDISR_EL2_Type := value_name
  (Mk_VDISR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF7E000000#64)))


def __get_ERRIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ERRIDR_EL1_Type := value_name
  (Mk_ERRIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_DISR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DISR_EL1_Type := value_name
  (Mk_DISR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF7E000000#64)))


def __get_ERRSELR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ERRSELR_EL1_Type := value_name
  (Mk_ERRSELR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_VSESR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VSESR_EL2_Type := value_name
  (Mk_VSESR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFE000000#64)))


def __get_BRBINF_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBINF_EL1_Type := value_name
  (Mk_BRBINF_EL1_Type (tmp &&& (Complement.complement 0xFFFF8000FFFCC01C#64)))


def __get_BRBCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBCR_EL2_Type := value_name
  (Mk_BRBCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF3FFC84#64)))


def __get_BRBFCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBFCR_EL1_Type := value_name
  (Mk_BRBFCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFCF80FF3F#64)))


def __get_BRBINFINJ_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBINFINJ_EL1_Type := value_name
  (Mk_BRBINFINJ_EL1_Type (tmp &&& (Complement.complement 0xFFFF8000FFFCC01C#64)))


def __get_BRBCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBCR_EL1_Type := value_name
  (Mk_BRBCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF3FFC84#64)))


def __get_BRBIDR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBIDR0_EL1_Type := value_name
  (Mk_BRBIDR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))


def __get_GCSPR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL3_Type := value_name
  (Mk_GCSPR_EL3_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x7#4 64)))))


def __get_GCSPR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL1_Type := value_name
  (Mk_GCSPR_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x7#4 64)))))


def __get_GCSCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCR_EL3_Type := value_name
  (Mk_GCSCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC9E#64)))


def __get_GCSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCR_EL1_Type := value_name
  (Mk_GCSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC9E#64)))


def __get_GCSPR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL2_Type := value_name
  (Mk_GCSPR_EL2_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x7#4 64)))))


def __get_GCSCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCR_EL2_Type := value_name
  (Mk_GCSCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC9E#64)))


def __get_GCSCRE0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCRE0_EL1_Type := value_name
  (Mk_GCSCRE0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF8DE#64)))


def __get_GCSPR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL0_Type := value_name
  (Mk_GCSPR_EL0_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0x7#4 64)))))


def __get_ICH_ELRSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_ELRSR_Type := value_name
  (Mk_ICH_ELRSR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))


def __get_ICC_IAR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IAR1_Type := value_name
  (Mk_ICC_IAR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_ICV_IGRPEN1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IGRPEN1_Type := value_name
  (Mk_ICV_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_CTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CTR_Type := value_name
  (Mk_CTR_Type ((tmp &&& (Complement.complement 0x40003FF0#32)) ||| 0x80000000#32))


def __get_PMUSERENR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMUSERENR_Type := value_name
  (Mk_PMUSERENR_Type (tmp &&& (Complement.complement 0xFFFFFF80#32)))


def __get_DBGAUTHSTATUS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGAUTHSTATUS_Type := value_name
  (Mk_DBGAUTHSTATUS_Type (tmp &&& (Complement.complement 0xF0FF0F00#32)))


def __get_ICC_IAR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IAR0_Type := value_name
  (Mk_ICC_IAR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_ICV_IGRPEN0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IGRPEN0_Type := value_name
  (Mk_ICV_IGRPEN0_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_ICV_CTLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_CTLR_Type := value_name
  (Mk_ICV_CTLR_Type (tmp &&& (Complement.complement 0xFFF300FC#32)))


def __get_HPFAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HPFAR_Type := value_name
  (Mk_HPFAR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0xF#4 32)))))


def __get_DBGCLAIMCLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGCLAIMCLR_Type := value_name
  (Mk_DBGCLAIMCLR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_DBGWVR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGWVR_Type := value_name
  (Mk_DBGWVR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x3#4 32)))))


def __get_ICV_HPPIR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_HPPIR1_Type := value_name
  (Mk_ICV_HPPIR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_HRMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HRMR_Type := value_name
  (Mk_HRMR_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))


def __get_ICH_VTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_VTR_Type := value_name
  (Mk_ICH_VTR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x3FFE0#20 32)))))


def __get_CSSELR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CSSELR_Type := value_name
  (Mk_CSSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))


def __get_CSSELR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CSSELR_Type := value_name
  (Mk_CSSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))


def __get_CSSELR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CSSELR_Type := value_name
  (Mk_CSSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))


def __get_DBGWCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGWCR_Type := value_name
  (Mk_DBGWCR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0xE00000#24 32)))))


def __get_ICH_VMCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_VMCR_Type := value_name
  (Mk_ICH_VMCR_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
        (Sail.BitVec.zeroExtend 0x3FDE0#20 32)))))


def __get_DBGDEVID1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDEVID1_Type := value_name
  (Mk_DBGDEVID1_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))


def __get_ICC_BPR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR1_Type := value_name
  (Mk_ICC_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICC_BPR1_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR1_Type := value_name
  (Mk_ICC_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICC_BPR1_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR1_Type := value_name
  (Mk_ICC_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_ICV_RPR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_RPR_Type := value_name
  (Mk_ICV_RPR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))


def __get_ICV_IAR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IAR1_Type := value_name
  (Mk_ICV_IAR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))


def __get_DBGPRCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGPRCR_Type := value_name
  (Mk_DBGPRCR_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))


def __get_SDER (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : SDER_Type := value_name
  (Mk_SDER_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))


def __get_ICC_BPR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR0_Type := value_name
  (Mk_ICC_BPR0_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))


def __get_CNTHCTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTHCTL_Type := value_name
  (Mk_CNTHCTL_Type (tmp &&& (Complement.complement 0xFFF00000#32)))


end ArmFull.Functions
