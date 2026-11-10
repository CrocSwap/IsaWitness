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

def _update_AMPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMUSERENR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMUSERENR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_BRBCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBFCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBIDR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBINFINJ_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBINFType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBINF_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBSRCINJ_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBSRCType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBSRC_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBTGTINJ_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBTGTType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBTGT_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_BRBTS_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CCSIDR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CCSIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CCSIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CCSIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CLIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CLIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTEL0ACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTFID0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTHCTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHCTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTHPS_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHPS_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTHPS_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHPS_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHP_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHP_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTHP_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHP_CVAL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHP_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHVS_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHVS_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTHVS_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHVS_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHV_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHV_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTHV_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTHV_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTKCTL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTKCTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTNSAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTPS_CTL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTPS_CVAL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTPS_TVAL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTP_CTL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTP_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTP_CVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTP_CVAL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTP_TVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTSCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTV_CTL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTV_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CNTV_CVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTV_CVAL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CNTV_TVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CONTEXTIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CONTEXTIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CONTEXTIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CPACR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CPACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CPTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CPTR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CSSELR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CSSELR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIAUTHSTATUS_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTICIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTICIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTICIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTICIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTICONTROL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIDEVARCH_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIDEVCTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIITCTRL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTILAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTILSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTIPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_CTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_CTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DACR32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGAUTHSTATUS_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGAUTHSTATUS_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGBCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGBCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGBVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGBVR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGBXVR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGCLAIMCLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGCLAIMCLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGCLAIMSET_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGCLAIMSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDCCINT_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDEVID1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDRAR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGDSCRext_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDSCRint_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDTRRXext_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDTRRXint_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDTRTXext_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDTRTXint_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGDTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGOSDLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGOSECCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGOSLAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGOSLSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGPRCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGPRCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGVCR32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGVCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGWCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGWCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DBGWVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DBGWVR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DCZID_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DFSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DISR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DSPSR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DSPSR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_DSPSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_DormantCtl_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDAA32PFR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_EDCIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDCIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDCIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDCIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDDEVARCH_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDDEVID1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDDFR1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_EDDFR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_EDECCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDECR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDESR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDHSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_EDITCTRL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDLAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDLSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPCSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_EDPFR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_EDPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPRCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDPRSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDRCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDSCR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDSCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_EDVIDSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ERRIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ERRIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ERRSELR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ERRSELR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ERRnFR_ElemType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ERXGSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ESRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ESR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ESR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_ESR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_FPCRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_FPCR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_FPEXC32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_FPEXC_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_FPSCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_FPSID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_FPSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSCRE0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSPR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSPR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSPR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GCSPR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_GICC_ABPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_GICC_AEOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


end ArmFull.Functions
