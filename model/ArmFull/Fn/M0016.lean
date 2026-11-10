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

def _get_BRBCR_EL1_Type_CC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_BRBCR_EL2_Type_CC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_BRBIDR0_EL1_Type_CC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_BRBINFINJ_EL1_Type_CC (v : (BitVec 64)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 45 32)


def _get_BRBINF_EL1_Type_CC (v : (BitVec 64)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 45 32)


def _get_PMCFGR_Type_CC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_BRBINFType_CCU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)


def _update_BRBINFType_CCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)


def _update_BRBINFINJ_EL1_Type_CCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)


def _update_BRBINF_EL1_Type_CCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)


def _get_BRBINFINJ_EL1_Type_CCU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)


def _get_BRBINF_EL1_Type_CCU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)


def _get_BRBINFType_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_BRBINFType_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_BRBINFINJ_EL1_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_BRBINF_EL1_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_EDPCSR_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 61 x)


def _update_EDSCR_Type_EL (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_PMPCSR_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 61 x)


def _get_BRBINFINJ_EL1_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _get_BRBINF_EL1_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _get_EDPCSR_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 62 61)


def _get_EDSCR_Type_EL (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_PMPCSR_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 62 61)


def _get_BRBINFType_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_BRBINFType_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_BRBFCR_EL1_Type_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_BRBINFINJ_EL1_Type_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_BRBINF_EL1_Type_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_BRBFCR_EL1_Type_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_BRBINFINJ_EL1_Type_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_BRBINF_EL1_Type_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_BRBINFType_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_BRBINFType_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_BRBCR_EL1_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_BRBCR_EL2_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_BRBINFINJ_EL1_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_BRBINF_EL1_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_BRBCR_EL1_Type_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_BRBCR_EL2_Type_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_BRBINFINJ_EL1_Type_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_BRBINF_EL1_Type_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_BRBINFType_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_BRBINFType_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_BRBINFINJ_EL1_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_BRBINF_EL1_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_DSPSR_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_DSPSR_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_PMCCFILTR_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_PMEVTYPER_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_PMICFILTR_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_PMPCSR_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_SPSR_EL1_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_EL2_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_EL3_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_abt_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_fiq_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_hyp_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_irq_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_mon_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_svc_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_und_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_BRBINFINJ_EL1_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_BRBINF_EL1_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_DSPSR_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_DSPSR_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_PMCCFILTR_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_PMEVTYPER_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_PMICFILTR_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_PMPCSR_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _get_SPSR_EL1_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_EL2_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_EL3_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_abt_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_fiq_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_hyp_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_irq_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_mon_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_svc_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_und_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_BRBINFType_TYPE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _update_BRBINFType_TYPE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def _update_BRBINFINJ_EL1_Type_TYPE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def _update_BRBINF_EL1_Type_TYPE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def _get_BRBINFINJ_EL1_Type_TYPE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _get_BRBINF_EL1_Type_TYPE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _get_BRBINFType_VALID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _update_BRBINFType_VALID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_BRBINFINJ_EL1_Type_VALID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_BRBINF_EL1_Type_VALID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _get_BRBINFINJ_EL1_Type_VALID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _get_BRBINF_EL1_Type_VALID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def undefined_Signal (ℓ : ChoiceLabel) (_ : Unit) : SailM Signal := do
  (internal_pick_at (ℓ.child 0) [Signal_Low, Signal_High])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def Signal_of_num (arg_ : Nat) : Signal :=
  match arg_ with
  | 0 => Signal_Low
  | _ => Signal_High


def num_of_Signal (arg_ : Signal) : Int :=
  match arg_ with
  | .Signal_Low => 0
  | .Signal_High => 1


def CYCLE_COUNTER_ID : Nat := 31


def INSTRUCTION_COUNTER_ID : Nat := 32


def PMU_EVENT_SW_INCR : (BitVec 16) := 0x0000#16


def PMU_EVENT_L1D_CACHE_REFILL : (BitVec 16) := 0x0003#16


def PMU_EVENT_L1D_CACHE : (BitVec 16) := 0x0004#16


def PMU_EVENT_INST_RETIRED : (BitVec 16) := 0x0008#16


def PMU_EVENT_EXC_TAKEN : (BitVec 16) := 0x0009#16


def PMU_EVENT_BR_MIS_PRED : (BitVec 16) := 0x0010#16


def PMU_EVENT_CPU_CYCLES : (BitVec 16) := 0x0011#16


def PMU_EVENT_INST_SPEC : (BitVec 16) := 0x001B#16


def PMU_EVENT_CHAIN : (BitVec 16) := 0x001E#16


def PMU_EVENT_BR_MIS_PRED_RETIRED : (BitVec 16) := 0x0022#16


def PMU_EVENT_L1D_TLB : (BitVec 16) := 0x0025#16


def PMU_EVENT_REMOTE_ACCESS : (BitVec 16) := 0x0031#16


def PMU_EVENT_LL_CACHE : (BitVec 16) := 0x0032#16


def PMU_EVENT_LL_CACHE_MISS : (BitVec 16) := 0x0033#16


def PMU_EVENT_DTLB_WALK : (BitVec 16) := 0x0034#16


def PMU_EVENT_L1D_CACHE_LMISS_RD : (BitVec 16) := 0x0039#16


def PMU_EVENT_L2D_CACHE_RD : (BitVec 16) := 0x0050#16


def PMU_EVENT_SAMPLE_POP : (BitVec 16) := 0x4000#16


def PMU_EVENT_SAMPLE_FEED : (BitVec 16) := 0x4001#16


def PMU_EVENT_SAMPLE_FILTRATE : (BitVec 16) := 0x4002#16


def PMU_EVENT_SAMPLE_COLLISION : (BitVec 16) := 0x4003#16


def PMU_EVENT_L2D_CACHE_LMISS_RD : (BitVec 16) := 0x4009#16


def PMU_EVENT_LDST_ALIGN_LAT : (BitVec 16) := 0x4020#16


def PMU_EVENT_SVE_PRED_EMPTY_SPEC : (BitVec 16) := 0x8075#16


def PMU_EVENT_SVE_PRED_PARTIAL_SPEC : (BitVec 16) := 0x8077#16


def PMU_EVENT_BRB_FILTRATE : (BitVec 16) := 0x811F#16


def PMU_EVENT_SAMPLE_WRAP : (BitVec 16) := 0x8123#16


def PMU_EVENT_SAMPLE_FEED_BR : (BitVec 16) := 0x812A#16


def PMU_EVENT_SAMPLE_FEED_LD : (BitVec 16) := 0x812B#16


def PMU_EVENT_SAMPLE_FEED_ST : (BitVec 16) := 0x812C#16


def PMU_EVENT_SAMPLE_FEED_OP : (BitVec 16) := 0x812D#16


def PMU_EVENT_SAMPLE_FEED_EVENT : (BitVec 16) := 0x812E#16


def PMU_EVENT_SAMPLE_FEED_LAT : (BitVec 16) := 0x812F#16


def PMU_EVENT_DSNP_HIT_RD : (BitVec 16) := 0x8194#16


def PMU_EVENT_L1D_CACHE_HITM_RD : (BitVec 16) := 0x8214#16


def PMU_EVENT_L2D_CACHE_HITM_RD : (BitVec 16) := 0x8215#16


def PMU_EVENT_L3D_CACHE_HITM_RD : (BitVec 16) := 0x8216#16


def PMU_EVENT_LL_CACHE_HITM_RD : (BitVec 16) := 0x8217#16


def PMU_EVENT_L1D_LFB_HIT_RD : (BitVec 16) := 0x8244#16


def PMU_EVENT_L2D_LFB_HIT_RD : (BitVec 16) := 0x8245#16


def PMU_EVENT_L3D_LFB_HIT_RD : (BitVec 16) := 0x8246#16


def PMU_EVENT_LL_LFB_HIT_RD : (BitVec 16) := 0x8247#16


def undefined_SecurityState (ℓ : ChoiceLabel) (_ : Unit) : SailM SecurityState := do
  (internal_pick_at (ℓ.child 0) [SS_NonSecure, SS_Root, SS_Realm, SS_Secure])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def SecurityState_of_num (arg_ : Nat) : SecurityState :=
  match arg_ with
  | 0 => SS_NonSecure
  | 1 => SS_Root
  | 2 => SS_Realm
  | _ => SS_Secure


def num_of_SecurityState (arg_ : SecurityState) : Int :=
  match arg_ with
  | .SS_NonSecure => 0
  | .SS_Root => 1
  | .SS_Realm => 2
  | .SS_Secure => 3


def M32_User : (BitVec 5) := 0b10000#5


def M32_FIQ : (BitVec 5) := 0b10001#5


def M32_IRQ : (BitVec 5) := 0b10010#5


def M32_Svc : (BitVec 5) := 0b10011#5


def M32_Monitor : (BitVec 5) := 0b10110#5


def M32_Abort : (BitVec 5) := 0b10111#5


def M32_Hyp : (BitVec 5) := 0b11010#5


def M32_Undef : (BitVec 5) := 0b11011#5


def M32_System : (BitVec 5) := 0b11111#5


def EL3 : (BitVec 2) := 0b11#2


def EL2 : (BitVec 2) := 0b10#2


def undefined_ProcState (ℓ : ChoiceLabel) (_ : Unit) : SailM ProcState := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 1) ) : SailM (BitVec 1) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 1) ) : SailM (BitVec 1) )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 9) 1) ) : SailM (BitVec 1) )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 1) ) : SailM (BitVec 1) )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 1) ) : SailM (BitVec 1) )
  let w__12 ← (( do (undefined_bitvector_at (ℓ.child 12) 1) ) : SailM (BitVec 1) )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 1) ) : SailM (BitVec 1) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 1) ) : SailM (BitVec 1) )
  let w__15 ← (( do (undefined_bitvector_at (ℓ.child 15) 2) ) : SailM (BitVec 2) )
  let w__16 ← (( do (undefined_bitvector_at (ℓ.child 16) 1) ) : SailM (BitVec 1) )
  let w__17 ← (( do (undefined_bitvector_at (ℓ.child 17) 1) ) : SailM (BitVec 1) )
  let w__18 ← (( do (undefined_bitvector_at (ℓ.child 18) 1) ) : SailM (BitVec 1) )
  let w__19 ← (( do (undefined_bitvector_at (ℓ.child 19) 1) ) : SailM (BitVec 1) )
  let w__20 ← (( do (undefined_bitvector_at (ℓ.child 20) 1) ) : SailM (BitVec 1) )
  let w__21 ← (( do (undefined_bitvector_at (ℓ.child 21) 2) ) : SailM (BitVec 2) )
  let w__22 ← (( do (undefined_bitvector_at (ℓ.child 22) 1) ) : SailM (BitVec 1) )
  let w__23 ← (( do (undefined_bitvector_at (ℓ.child 23) 1) ) : SailM (BitVec 1) )
  let w__24 ← (( do (undefined_bitvector_at (ℓ.child 24) 1) ) : SailM (BitVec 1) )
  let w__25 ← (( do (undefined_bitvector_at (ℓ.child 25) 4) ) : SailM (BitVec 4) )
  let w__26 ← (( do (undefined_bitvector_at (ℓ.child 26) 1) ) : SailM (BitVec 1) )
  let w__27 ← (( do (undefined_bitvector_at (ℓ.child 27) 8) ) : SailM (BitVec 8) )
  let w__28 ← (( do (undefined_bitvector_at (ℓ.child 28) 1) ) : SailM (BitVec 1) )
  let w__29 ← (( do (undefined_bitvector_at (ℓ.child 29) 1) ) : SailM (BitVec 1) )
  let w__30 ← (( do (undefined_bitvector_at (ℓ.child 30) 1) ) : SailM (BitVec 1) )
  let w__31 ← (( do (undefined_bitvector_at (ℓ.child 31) 5) ) : SailM (BitVec 5) )
  (pure ({ N := w__0
           Z := w__1
           C := w__2
           V := w__3
           D := w__4
           A := w__5
           I := w__6
           F := w__7
           EXLOCK := w__8
           PAN := w__9
           UAO := w__10
           DIT := w__11
           TCO := w__12
           PM := w__13
           PPEND := w__14
           BTYPE := w__15
           ZA := w__16
           SM := w__17
           ALLINT := w__18
           SS := w__19
           IL := w__20
           EL := w__21
           nRW := w__22
           SP := w__23
           Q := w__24
           GE := w__25
           SSBS := w__26
           IT := w__27
           J := w__28
           T := w__29
           E := w__30
           M := w__31 }))


def undefined_PrivilegeLevel (ℓ : ChoiceLabel) (_ : Unit) : SailM PrivilegeLevel := do
  (internal_pick_at (ℓ.child 0) [PL3, PL2, PL1, PL0])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PrivilegeLevel_of_num (arg_ : Nat) : PrivilegeLevel :=
  match arg_ with
  | 0 => PL3
  | 1 => PL2
  | 2 => PL1
  | _ => PL0


def num_of_PrivilegeLevel (arg_ : PrivilegeLevel) : Int :=
  match arg_ with
  | .PL3 => 0
  | .PL2 => 1
  | .PL1 => 2
  | .PL0 => 3


def undefined_InstrSet (ℓ : ChoiceLabel) (_ : Unit) : SailM InstrSet := do
  (internal_pick_at (ℓ.child 0) [InstrSet_A64, InstrSet_A32, InstrSet_T32])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def InstrSet_of_num (arg_ : Nat) : InstrSet :=
  match arg_ with
  | 0 => InstrSet_A64
  | 1 => InstrSet_A32
  | _ => InstrSet_T32


def num_of_InstrSet (arg_ : InstrSet) : Int :=
  match arg_ with
  | .InstrSet_A64 => 0
  | .InstrSet_A32 => 1
  | .InstrSet_T32 => 2


def undefined_DSBAlias (ℓ : ChoiceLabel) (_ : Unit) : SailM DSBAlias := do
  (internal_pick_at (ℓ.child 0) [DSBAlias_SSBB, DSBAlias_PSSBB, DSBAlias_DSB])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def DSBAlias_of_num (arg_ : Nat) : DSBAlias :=
  match arg_ with
  | 0 => DSBAlias_SSBB
  | 1 => DSBAlias_PSSBB
  | _ => DSBAlias_DSB


def num_of_DSBAlias (arg_ : DSBAlias) : Int :=
  match arg_ with
  | .DSBAlias_SSBB => 0
  | .DSBAlias_PSSBB => 1
  | .DSBAlias_DSB => 2


def undefined_WFxType (ℓ : ChoiceLabel) (_ : Unit) : SailM WFxType := do
  (internal_pick_at (ℓ.child 0) [WFxType_WFE, WFxType_WFI, WFxType_WFET, WFxType_WFIT])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def WFxType_of_num (arg_ : Nat) : WFxType :=
  match arg_ with
  | 0 => WFxType_WFE
  | 1 => WFxType_WFI
  | 2 => WFxType_WFET
  | _ => WFxType_WFIT


def num_of_WFxType (arg_ : WFxType) : Int :=
  match arg_ with
  | .WFxType_WFE => 0
  | .WFxType_WFI => 1
  | .WFxType_WFET => 2
  | .WFxType_WFIT => 3


def undefined_ExceptionalOccurrenceTargetState (ℓ : ChoiceLabel) (_ : Unit) : SailM ExceptionalOccurrenceTargetState := do
  (internal_pick_at (ℓ.child 0) [AArch32_NonDebugState, AArch64_NonDebugState, DebugState])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def ExceptionalOccurrenceTargetState_of_num (arg_ : Nat) : ExceptionalOccurrenceTargetState :=
  match arg_ with
  | 0 => AArch32_NonDebugState
  | 1 => AArch64_NonDebugState
  | _ => DebugState


def num_of_ExceptionalOccurrenceTargetState (arg_ : ExceptionalOccurrenceTargetState) : Int :=
  match arg_ with
  | .AArch32_NonDebugState => 0
  | .AArch64_NonDebugState => 1
  | .DebugState => 2


def __UNKNOWN_PARTIDtype (_ : Unit) : SailM (BitVec 16) := do
  (undefined_bitvector_at (← occLabel 70) 16)


def __UNKNOWN_PMGtype (_ : Unit) : SailM (BitVec 8) := do
  (undefined_bitvector_at (← occLabel 71) 8)


def undefined_PARTIDspaceType (ℓ : ChoiceLabel) (_ : Unit) : SailM PARTIDspaceType := do
  (internal_pick_at (ℓ.child 0)
    [PIdSpace_Secure, PIdSpace_Root, PIdSpace_Realm, PIdSpace_NonSecure])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PARTIDspaceType_of_num (arg_ : Nat) : PARTIDspaceType :=
  match arg_ with
  | 0 => PIdSpace_Secure
  | 1 => PIdSpace_Root
  | 2 => PIdSpace_Realm
  | _ => PIdSpace_NonSecure


def num_of_PARTIDspaceType (arg_ : PARTIDspaceType) : Int :=
  match arg_ with
  | .PIdSpace_Secure => 0
  | .PIdSpace_Root => 1
  | .PIdSpace_Realm => 2
  | .PIdSpace_NonSecure => 3


def undefined_AccessType (ℓ : ChoiceLabel) (_ : Unit) : SailM AccessType := do
  (internal_pick_at (ℓ.child 0)
    [AccessType_IFETCH, AccessType_GPR, AccessType_ASIMD, AccessType_SVE, AccessType_SME, AccessType_IC, AccessType_DC, AccessType_DCZero, AccessType_AT, AccessType_NV2, AccessType_SPE, AccessType_GCS, AccessType_GPTW, AccessType_TTW])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 13 -/
def AccessType_of_num (arg_ : Nat) : AccessType :=
  match arg_ with
  | 0 => AccessType_IFETCH
  | 1 => AccessType_GPR
  | 2 => AccessType_ASIMD
  | 3 => AccessType_SVE
  | 4 => AccessType_SME
  | 5 => AccessType_IC
  | 6 => AccessType_DC
  | 7 => AccessType_DCZero
  | 8 => AccessType_AT
  | 9 => AccessType_NV2
  | 10 => AccessType_SPE
  | 11 => AccessType_GCS
  | 12 => AccessType_GPTW
  | _ => AccessType_TTW


end ArmFull.Functions
