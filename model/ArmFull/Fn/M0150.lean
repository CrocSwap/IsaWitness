module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0143
public import ArmFull.Fn.M0144 set_option backward.proofsInPublic true @[expose] public section

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

def decode_aarch32_instrs_YIELD_T2enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_YIELD_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_SEVL_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:43243.29-43243.30"
      (execute_aarch32_instrs_SEVL_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SEVL_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_SEVL_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SEVL_T2enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_SEVL_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_CSDB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:46109.29-46109.30"
      if ((cond != 0b1110#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CSDB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SSBB_A1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_SSBB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_PSSBB_A1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_PSSBB_Op_A_txt ())
    else ()
  (pure (()))


def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg FEAT_AA32EL0_IMPLEMENTED true
  writeReg FEAT_AA32EL1_IMPLEMENTED false
  writeReg FEAT_AA32EL2_IMPLEMENTED false
  writeReg FEAT_AA32EL3_IMPLEMENTED false
  writeReg FEAT_AA64EL0_IMPLEMENTED true
  writeReg FEAT_AA64EL1_IMPLEMENTED true
  writeReg FEAT_AA64EL2_IMPLEMENTED true
  writeReg FEAT_AA64EL3_IMPLEMENTED true
  writeReg FEAT_EL0_IMPLEMENTED true
  writeReg FEAT_EL1_IMPLEMENTED true
  writeReg FEAT_EL2_IMPLEMENTED true
  writeReg FEAT_EL3_IMPLEMENTED true
  writeReg FEAT_AES_IMPLEMENTED true
  writeReg FEAT_AdvSIMD_IMPLEMENTED true
  writeReg FEAT_CSV2_1p1_IMPLEMENTED true
  writeReg FEAT_CSV2_1p2_IMPLEMENTED true
  writeReg FEAT_CSV2_2_IMPLEMENTED true
  writeReg FEAT_CSV2_3_IMPLEMENTED true
  writeReg FEAT_DoubleLock_IMPLEMENTED true
  writeReg FEAT_ETMv4_IMPLEMENTED false
  writeReg FEAT_ETMv4p1_IMPLEMENTED true
  writeReg FEAT_ETMv4p2_IMPLEMENTED true
  writeReg FEAT_ETMv4p3_IMPLEMENTED true
  writeReg FEAT_ETMv4p4_IMPLEMENTED true
  writeReg FEAT_ETMv4p5_IMPLEMENTED true
  writeReg FEAT_ETMv4p6_IMPLEMENTED true
  writeReg FEAT_ETS2_IMPLEMENTED true
  writeReg FEAT_FP_IMPLEMENTED true
  writeReg FEAT_GICv3_IMPLEMENTED true
  writeReg FEAT_GICv3_LEGACY_IMPLEMENTED true
  writeReg FEAT_GICv3_TDIR_IMPLEMENTED true
  writeReg FEAT_GICv3p1_IMPLEMENTED true
  writeReg FEAT_GICv4_IMPLEMENTED true
  writeReg FEAT_GICv4p1_IMPLEMENTED true
  writeReg FEAT_IVIPT_IMPLEMENTED true
  writeReg FEAT_PCSRv8_IMPLEMENTED true
  writeReg FEAT_PMULL_IMPLEMENTED true
  writeReg FEAT_PMUv3_IMPLEMENTED true
  writeReg FEAT_PMUv3_EXT_IMPLEMENTED true
  writeReg FEAT_PMUv3_EXT32_IMPLEMENTED true
  writeReg FEAT_SHA1_IMPLEMENTED true
  writeReg FEAT_SHA256_IMPLEMENTED true
  writeReg FEAT_TRC_EXT_IMPLEMENTED true
  writeReg FEAT_TRC_SR_IMPLEMENTED true
  writeReg FEAT_nTLBPA_IMPLEMENTED true
  writeReg FEAT_CRC32_IMPLEMENTED true
  writeReg FEAT_Debugv8p1_IMPLEMENTED true
  writeReg FEAT_HAFDBS_IMPLEMENTED true
  writeReg FEAT_HPDS_IMPLEMENTED true
  writeReg FEAT_LOR_IMPLEMENTED true
  writeReg FEAT_LSE_IMPLEMENTED true
  writeReg FEAT_PAN_IMPLEMENTED true
  writeReg FEAT_PMUv3p1_IMPLEMENTED true
  writeReg FEAT_RDM_IMPLEMENTED true
  writeReg FEAT_VHE_IMPLEMENTED true
  writeReg FEAT_VMID16_IMPLEMENTED true
  writeReg FEAT_AA32BF16_IMPLEMENTED true
  writeReg FEAT_AA32HPD_IMPLEMENTED true
  writeReg FEAT_AA32I8MM_IMPLEMENTED true
  writeReg FEAT_ASMv8p2_IMPLEMENTED true
  writeReg FEAT_DPB_IMPLEMENTED true
  writeReg FEAT_Debugv8p2_IMPLEMENTED true
  writeReg FEAT_EDHSR_IMPLEMENTED true
  writeReg FEAT_F32MM_IMPLEMENTED true
  writeReg FEAT_F64MM_IMPLEMENTED true
  writeReg FEAT_FP16_IMPLEMENTED true
  writeReg FEAT_HPDS2_IMPLEMENTED true
  writeReg FEAT_I8MM_IMPLEMENTED true
  writeReg FEAT_IESB_IMPLEMENTED true
  writeReg FEAT_LPA_IMPLEMENTED true
  writeReg FEAT_LSMAOC_IMPLEMENTED true
  writeReg FEAT_LVA_IMPLEMENTED true
  writeReg FEAT_MPAM_IMPLEMENTED true
  writeReg FEAT_PAN2_IMPLEMENTED true
  writeReg FEAT_PCSRv8p2_IMPLEMENTED true
  writeReg FEAT_RAS_IMPLEMENTED true
  writeReg FEAT_SHA3_IMPLEMENTED true
  writeReg FEAT_SHA512_IMPLEMENTED true
  writeReg FEAT_SM3_IMPLEMENTED true
  writeReg FEAT_SM4_IMPLEMENTED true
  writeReg FEAT_SPE_IMPLEMENTED true
  writeReg FEAT_SVE_IMPLEMENTED true
  writeReg FEAT_TTCNP_IMPLEMENTED true
  writeReg FEAT_UAO_IMPLEMENTED true
  writeReg FEAT_VPIPT_IMPLEMENTED true
  writeReg FEAT_XNX_IMPLEMENTED true
  writeReg FEAT_CCIDX_IMPLEMENTED true
  writeReg FEAT_CONSTPACFIELD_IMPLEMENTED false
  writeReg FEAT_EPAC_IMPLEMENTED false
  writeReg FEAT_FCMA_IMPLEMENTED true
  writeReg FEAT_FPAC_IMPLEMENTED true
  writeReg FEAT_FPACCOMBINE_IMPLEMENTED true
  writeReg FEAT_JSCVT_IMPLEMENTED true
  writeReg FEAT_LRCPC_IMPLEMENTED true
  writeReg FEAT_NV_IMPLEMENTED true
  writeReg FEAT_PACIMP_IMPLEMENTED false
  writeReg FEAT_PACQARMA3_IMPLEMENTED false
  writeReg FEAT_PACQARMA5_IMPLEMENTED true
  writeReg FEAT_PAuth_IMPLEMENTED true
  writeReg FEAT_SPEv1p1_IMPLEMENTED true
  writeReg FEAT_AMUv1_IMPLEMENTED true
  writeReg FEAT_BBM_IMPLEMENTED true
  writeReg FEAT_CNTSC_IMPLEMENTED true
  writeReg FEAT_DIT_IMPLEMENTED true
  writeReg FEAT_Debugv8p4_IMPLEMENTED true
  writeReg FEAT_DotProd_IMPLEMENTED true
  writeReg FEAT_DoubleFault_IMPLEMENTED true
  writeReg FEAT_FHM_IMPLEMENTED true
  writeReg FEAT_FlagM_IMPLEMENTED true
  writeReg FEAT_IDST_IMPLEMENTED true
  writeReg FEAT_LRCPC2_IMPLEMENTED true
  writeReg FEAT_LSE2_IMPLEMENTED true
  writeReg FEAT_NV2_IMPLEMENTED true
  writeReg FEAT_PMUv3p4_IMPLEMENTED true
  writeReg FEAT_RASSAv1p1_IMPLEMENTED true
  writeReg FEAT_RASv1p1_IMPLEMENTED true
  writeReg FEAT_S2FWB_IMPLEMENTED true
  writeReg FEAT_SEL2_IMPLEMENTED true
  writeReg FEAT_TLBIOS_IMPLEMENTED true
  writeReg FEAT_TLBIRANGE_IMPLEMENTED true
  writeReg FEAT_TRF_IMPLEMENTED true
  writeReg FEAT_TTL_IMPLEMENTED true
  writeReg FEAT_TTST_IMPLEMENTED true
  writeReg FEAT_BTI_IMPLEMENTED true
  writeReg FEAT_CSV2_IMPLEMENTED true
  writeReg FEAT_CSV3_IMPLEMENTED true
  writeReg FEAT_DPB2_IMPLEMENTED true
  writeReg FEAT_E0PD_IMPLEMENTED true
  writeReg FEAT_EVT_IMPLEMENTED true
  writeReg FEAT_ExS_IMPLEMENTED true
  writeReg FEAT_FRINTTS_IMPLEMENTED true
  writeReg FEAT_FlagM2_IMPLEMENTED true
  writeReg FEAT_GTG_IMPLEMENTED true
  writeReg FEAT_MTE_IMPLEMENTED true
  writeReg FEAT_MTE2_IMPLEMENTED true
  writeReg FEAT_PMUv3p5_IMPLEMENTED true
  writeReg FEAT_RNG_IMPLEMENTED true
  writeReg FEAT_RNG_TRAP_IMPLEMENTED true
  writeReg FEAT_SB_IMPLEMENTED true
  writeReg FEAT_SPECRES_IMPLEMENTED true
  writeReg FEAT_SSBS_IMPLEMENTED true
  writeReg FEAT_SSBS2_IMPLEMENTED true
  writeReg FEAT_AMUv1p1_IMPLEMENTED true
  writeReg FEAT_BF16_IMPLEMENTED true
  writeReg FEAT_DGH_IMPLEMENTED true
  writeReg FEAT_ECV_IMPLEMENTED true
  writeReg FEAT_FGT_IMPLEMENTED true
  writeReg FEAT_HPMN0_IMPLEMENTED true
  writeReg FEAT_MPAMv0p1_IMPLEMENTED true
  writeReg FEAT_MPAMv1p1_IMPLEMENTED true
  writeReg FEAT_MTPMU_IMPLEMENTED true
  writeReg FEAT_PAuth2_IMPLEMENTED true
  writeReg FEAT_TWED_IMPLEMENTED true
  writeReg FEAT_AFP_IMPLEMENTED true
  writeReg FEAT_EBF16_IMPLEMENTED true
  writeReg FEAT_HCX_IMPLEMENTED true
  writeReg FEAT_LPA2_IMPLEMENTED true
  writeReg FEAT_LS64_IMPLEMENTED true
  writeReg FEAT_LS64_ACCDATA_IMPLEMENTED true
  writeReg FEAT_LS64_V_IMPLEMENTED true
  writeReg FEAT_MTE3_IMPLEMENTED true
  writeReg FEAT_PAN3_IMPLEMENTED true
  writeReg FEAT_PMUv3p7_IMPLEMENTED true
  writeReg FEAT_RPRES_IMPLEMENTED true
  writeReg FEAT_SPEv1p2_IMPLEMENTED true
  writeReg FEAT_WFxT_IMPLEMENTED true
  writeReg FEAT_XS_IMPLEMENTED true
  writeReg FEAT_CMOW_IMPLEMENTED true
  writeReg FEAT_Debugv8p8_IMPLEMENTED true
  writeReg FEAT_GICv3_NMI_IMPLEMENTED true
  writeReg FEAT_HBC_IMPLEMENTED true
  writeReg FEAT_MOPS_IMPLEMENTED true
  writeReg FEAT_NMI_IMPLEMENTED true
  writeReg FEAT_PMUv3_EXT64_IMPLEMENTED true
  writeReg FEAT_PMUv3_TH_IMPLEMENTED true
  writeReg FEAT_PMUv3p8_IMPLEMENTED true
  writeReg FEAT_SCTLR2_IMPLEMENTED true
  writeReg FEAT_SPEv1p3_IMPLEMENTED true
  writeReg FEAT_TCR2_IMPLEMENTED true
  writeReg FEAT_TIDCP1_IMPLEMENTED true
  writeReg FEAT_ADERR_IMPLEMENTED true
  writeReg FEAT_AIE_IMPLEMENTED true
  writeReg FEAT_ANERR_IMPLEMENTED true
  writeReg FEAT_CLRBHB_IMPLEMENTED true
  writeReg FEAT_CSSC_IMPLEMENTED true
  writeReg FEAT_Debugv8p9_IMPLEMENTED true
  writeReg FEAT_DoubleFault2_IMPLEMENTED true
  writeReg FEAT_ECBHB_IMPLEMENTED true
  writeReg FEAT_FGT2_IMPLEMENTED true
  writeReg FEAT_HAFT_IMPLEMENTED true
  writeReg FEAT_LRCPC3_IMPLEMENTED true
  writeReg FEAT_MTE4_IMPLEMENTED true
  writeReg FEAT_MTE_ASYM_FAULT_IMPLEMENTED true
  writeReg FEAT_MTE_ASYNC_IMPLEMENTED true
  writeReg FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED true
  writeReg FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED true
  writeReg FEAT_MTE_PERM_IMPLEMENTED true
  writeReg FEAT_MTE_STORE_ONLY_IMPLEMENTED true
  writeReg FEAT_MTE_TAGGED_FAR_IMPLEMENTED true
  writeReg FEAT_PCSRv8p9_IMPLEMENTED true
  writeReg FEAT_PFAR_IMPLEMENTED true
  writeReg FEAT_PMUv3_EDGE_IMPLEMENTED true
  writeReg FEAT_PMUv3_ICNTR_IMPLEMENTED true
  writeReg FEAT_PMUv3_SS_IMPLEMENTED true
  writeReg FEAT_PMUv3p9_IMPLEMENTED true
  writeReg FEAT_PRFMSLC_IMPLEMENTED true
  writeReg FEAT_RASSAv2_IMPLEMENTED true
  writeReg FEAT_RASv2_IMPLEMENTED true
  writeReg FEAT_RPRFM_IMPLEMENTED true
  writeReg FEAT_S1PIE_IMPLEMENTED true
  writeReg FEAT_S1POE_IMPLEMENTED true
  writeReg FEAT_S2PIE_IMPLEMENTED true
  writeReg FEAT_S2POE_IMPLEMENTED true
  writeReg FEAT_SPECRES2_IMPLEMENTED true
  writeReg FEAT_SPE_CRR_IMPLEMENTED true
  writeReg FEAT_SPE_FDS_IMPLEMENTED true
  writeReg FEAT_SPEv1p4_IMPLEMENTED true
  writeReg FEAT_SPMU_IMPLEMENTED true
  writeReg FEAT_THE_IMPLEMENTED true
  writeReg FEAT_DoPD_IMPLEMENTED true
  writeReg FEAT_ETE_IMPLEMENTED true
  writeReg FEAT_SVE2_IMPLEMENTED true
  writeReg FEAT_SVE_AES_IMPLEMENTED true
  writeReg FEAT_SVE_BitPerm_IMPLEMENTED true
  writeReg FEAT_SVE_PMULL128_IMPLEMENTED true
  writeReg FEAT_SVE_SHA3_IMPLEMENTED true
  writeReg FEAT_SVE_SM4_IMPLEMENTED true
  writeReg FEAT_TME_IMPLEMENTED true
  writeReg FEAT_TRBE_IMPLEMENTED true
  writeReg FEAT_ETEv1p1_IMPLEMENTED true
  writeReg FEAT_BRBE_IMPLEMENTED true
  writeReg FEAT_ETEv1p2_IMPLEMENTED true
  writeReg FEAT_RME_IMPLEMENTED true
  writeReg FEAT_SME_IMPLEMENTED true
  writeReg FEAT_SME_F64F64_IMPLEMENTED true
  writeReg FEAT_SME_FA64_IMPLEMENTED true
  writeReg FEAT_SME_I16I64_IMPLEMENTED true
  writeReg FEAT_BRBEv1p1_IMPLEMENTED true
  writeReg FEAT_MEC_IMPLEMENTED true
  writeReg FEAT_SME2_IMPLEMENTED true
  writeReg FEAT_ABLE_IMPLEMENTED true
  writeReg FEAT_CHK_IMPLEMENTED true
  writeReg FEAT_D128_IMPLEMENTED true
  writeReg FEAT_EBEP_IMPLEMENTED true
  writeReg FEAT_ETEv1p3_IMPLEMENTED true
  writeReg FEAT_GCS_IMPLEMENTED true
  writeReg FEAT_ITE_IMPLEMENTED true
  writeReg FEAT_LSE128_IMPLEMENTED true
  writeReg FEAT_LVA3_IMPLEMENTED true
  writeReg FEAT_SEBEP_IMPLEMENTED true
  writeReg FEAT_SME2p1_IMPLEMENTED true
  writeReg FEAT_SME_F16F16_IMPLEMENTED true
  writeReg FEAT_SVE2p1_IMPLEMENTED true
  writeReg FEAT_SVE_B16B16_IMPLEMENTED true
  writeReg FEAT_SYSINSTR128_IMPLEMENTED true
  writeReg FEAT_SYSREG128_IMPLEMENTED true
  writeReg FEAT_TRBE_EXT_IMPLEMENTED true
  writeReg FEAT_TRBE_MPAM_IMPLEMENTED true
  writeReg v8Ap0_IMPLEMENTED true
  writeReg v8Ap1_IMPLEMENTED true
  writeReg v8Ap2_IMPLEMENTED true
  writeReg v8Ap3_IMPLEMENTED true
  writeReg v8Ap4_IMPLEMENTED true
  writeReg v8Ap5_IMPLEMENTED true
  writeReg v8Ap6_IMPLEMENTED true
  writeReg v8Ap7_IMPLEMENTED true
  writeReg v8Ap8_IMPLEMENTED true
  writeReg v8Ap9_IMPLEMENTED true
  writeReg v9Ap0_IMPLEMENTED true
  writeReg v9Ap1_IMPLEMENTED true
  writeReg v9Ap2_IMPLEMENTED true
  writeReg v9Ap3_IMPLEMENTED true
  writeReg v9Ap4_IMPLEMENTED true
  writeReg NUM_BREAKPOINTS (Neg.neg 1)
  writeReg NUM_WATCHPOINTS (Neg.neg 1)
  let w__0 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  writeReg __num_ctx_breakpoints w__0
  writeReg NUM_AMU_COUNTER_GROUPS 2
  writeReg NUM_AMU_CG0_MONITORS 4
  writeReg NUM_AMU_CG1_MONITORS 16
  writeReg NUM_PMU_COUNTERS 31
  writeReg NUM_BRBE_RECORDS 64
  writeReg NUM_GIC_PREEMPTION_BITS 5
  writeReg NUM_GIC_PRIORITY_BITS 5
  writeReg NUM_GIC_LIST_REGS 16
  writeReg __apply_effective_shareability true
  writeReg __cpy_mops_option_a_supported true
  writeReg __cpyf_mops_option_a_supported true
  writeReg __empam_force_ns_RAO false
  writeReg __empam_force_ns_implemented false
  writeReg __empam_sdeflt_implemented false
  writeReg __empam_tidr_implemented false
  writeReg __feat_rpres true
  writeReg __has_sme_priority_control true
  writeReg __isb_is_branch true
  writeReg __mpam_frac CFG_MPAM_frac_none
  writeReg __mpam_major CFG_MPAM_none
  writeReg __mte_implemented 0b0010#4
  writeReg __set_mops_option_a_supported true
  writeReg __setg_mops_option_a_supported true
  writeReg __sme_only false
  let w__1 ← (( do (undefined_bool_at (.site 8674) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_0 (w__1 : Bool)
  let w__2 ← (( do (undefined_bool_at (.site 8675) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_1 (w__2 : Bool)
  let w__3 ← (( do (undefined_bool_at (.site 8676) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_11 (w__3 : Bool)
  let w__4 ← (( do (undefined_bool_at (.site 8677) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_2 (w__4 : Bool)
  let w__5 ← (( do (undefined_bool_at (.site 8678) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_3 (w__5 : Bool)
  let w__6 ← (( do (undefined_bool_at (.site 8679) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_4 (w__6 : Bool)
  let w__7 ← (( do (undefined_bool_at (.site 8680) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_5 (w__7 : Bool)
  let w__8 ← (( do (undefined_bool_at (.site 8681) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_6 (w__8 : Bool)
  let w__9 ← (( do (undefined_bool_at (.site 8682) ()) ) : SailM Bool )
  writeReg C40_IMPDEF_BOOL_9 (w__9 : Bool)
  let w__10 ← (( do (undefined_bool_at (.site 8683) ()) ) : SailM Bool )
  writeReg C47_IMPDEF_TRANSACTIONAL_SYSREG_ACCESS (w__10 : Bool)
  writeReg __block_bbm_implemented (BitVec.toNat 0x2#4)
  writeReg __has_sve_extended_bf16 2
  writeReg __max_implemented_smeveclen 512
  writeReg __max_implemented_sveveclen 2048
  writeReg __supported_pa_size 56
  writeReg CFG_RVBAR (Sail.BitVec.zeroExtend 0x0#4 64)
  writeReg __impdef_TG0 0b00#2
  writeReg __impdef_TG1 0b10#2
  writeReg __mpam_has_hcr true
  writeReg __mpam_partid_max (Zeros (n := 16))
  writeReg __mpam_pmg_max (Zeros (n := 8))
  writeReg __mpam_vpmr_max (Zeros (n := 3))
  writeReg __GIC_Active none
  writeReg __GIC_Pending none
  writeReg __tlb_enabled false
  writeReg __exclusive_granule_size 0b0100#4
  writeReg CFG_MPIDR 0x80000000#32
  writeReg __CNTbase_frequency 0x05F5E100#32
  writeReg __dczid_log2_block_size (BitVec.toNat 0x8#4)
  writeReg __gmid_log2_block_size (BitVec.toNat 0x4#4)
  writeReg __mecid_width 0x0#4
  writeReg __mpam_has_altsp true
  writeReg __rme_l0gptsz (Zeros (n := 4))
  writeReg __supported_va_size 56
  writeReg __g1_activity_monitor_implemented 0x0000#16
  writeReg __g1_activity_monitor_offset_implemented 0x0000#16
  writeReg __CTIBase (integer_subrange (BitVec.toNat 0x22020000#32) (56 -i 1) 0)
  writeReg __CNTControlBase (integer_subrange (BitVec.toNat 0x16200000#32) (56 -i 1) 0)
  writeReg __ExtDebugBase (integer_subrange (BitVec.toNat 0x22010000#32) (56 -i 1) 0)
  writeReg __GICCPUInterfaceBase (integer_subrange (BitVec.toNat 0x13082000#32) (56 -i 1) 0)
  writeReg __GICDistBase (integer_subrange (BitVec.toNat 0x2C010000#32) (56 -i 1) 0)
  writeReg __GICITSControlBase (integer_subrange (BitVec.toNat 0x2C120000#32) (56 -i 1) 0)
  writeReg __PMUBase (integer_subrange (BitVec.toNat 0x22030000#32) (56 -i 1) 0)
  writeReg __syncAbortOnReadNormCache true
  writeReg __syncAbortOnReadNormNonCache true
  writeReg __syncAbortOnDeviceRead true
  writeReg __syncAbortOnSoRead true
  writeReg __syncAbortOnSoWrite true
  writeReg __syncAbortOnPrefetch true
  writeReg __syncAbortOnTTWCache true
  writeReg __syncAbortOnTTWNonCache true
  writeReg __syncAbortOnWriteNormCache false
  writeReg __syncAbortOnWriteNormNonCache false
  writeReg __syncAbortOnDeviceWrite false
  writeReg __unpred_tsize_aborts true
  writeReg __ignore_rvbar_in_aarch32 false
  writeReg __trickbox_enabled false
  writeReg __mops_forward_copy true
  writeReg __DBG_ROM_ADDR (integer_subrange (BitVec.toNat 0x22000000#32) (56 -i 1) 0)
  writeReg CFG_RMR_AA64 1#1
  writeReg ZCR_EL3_LEN_VALUE (Neg.neg 1)
  writeReg CPTR_EL3_EZ_VALUE (Neg.neg 1)
  writeReg CPTR_EL3_ESM_VALUE (Neg.neg 1)
  writeReg SMCR_EL3_LEN_VALUE (Neg.neg 1)
  writeReg __has_spe_pseudo_cycles false
  writeReg HEAP_BASE (Sail.BitVec.zeroExtend 0x00000000#32 64)
  writeReg HEAP_LIMIT (Sail.BitVec.zeroExtend 0x0F000000#32 64)
  writeReg STACK_BASE (Sail.BitVec.zeroExtend 0x10000000#32 64)
  writeReg STACK_LIMIT (Sail.BitVec.zeroExtend 0x0F000000#32 64)
  writeReg __emulator_termination_opcode none
  (initialize_registers ())


/-- Type quantifiers: k_n : Nat, hi : Int, lo : Int, l' : Int, k_n ≥ 0 ∧
  (Sail.Int.toNatChecked ((((hi : Int) -i (lo : Int)) +i (1 : Int)) +i (l' : Int))) ≥ 0 -/
def subrange_zeros_concat (xs : (BitVec k_n)) (hi : Int) (lo : Int) (l' : Int) : (BitVec (Sail.Int.toNatChecked ((((hi : Int) -i (lo : Int)) +i (1 : Int)) +i (l' : Int)))) :=
  (Sail.BitVec.castWidth (slice_zeros_concat xs lo ((hi -i lo) +i 1) l'))


/-- Type quantifiers: lo : Int, hi : Int, n : Nat, n ≥ 0 -/
def set_subrange_zeros {n : _} (xs : (BitVec n)) (hi : Int) (lo : Int) : (BitVec n) :=
  (Sail.BitVec.castWidth (set_slice_zeros (n := n) (Sail.BitVec.castWidth xs) lo ((hi -i lo) +i 1)))


/-- Type quantifiers: j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def zext_subrange {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) : (BitVec m) :=
  (Sail.BitVec.castWidth (zext_slice (m := m) xs j ((i -i j) +i 1)))


/-- Type quantifiers: j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def sext_subrange {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) : (BitVec m) :=
  (Sail.BitVec.castWidth (sext_slice (m := m) xs j ((i -i j) +i 1)))


/-- Type quantifiers: shift : Int, l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_slice_signed {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) (shift : Int) : (BitVec m) :=
  (Sail.BitVec.castWidth ((sext_slice (m := m) xs i l) <<< shift))


/-- Type quantifiers: i : Int, n1 : Nat, s1 : Nat, e1 : Nat, s2 : Nat, e2 : Nat, 0 ≤ e1 ∧
  e1 ≤ s1 ∧ s1 < n1 ∧ 0 ≤ e2 ∧ e2 ≤ s2 ∧ (s1 - e1) = (s2 - e2) -/
def vector_update_subrange_from_integer_subrange {n1 : _} (v1 : (BitVec n1)) (s1 : Nat) (e1 : Nat) (i : Int) (s2 : Nat) (e2 : Nat) : (BitVec n1) :=
  let v2 : (BitVec n1) := (Sail.BitVec.castWidth (get_slice_int n1 i e2))
  (Sail.BitVec.castWidth (vector_update_subrange_from_subrange (n := n1) (Sail.BitVec.castWidth v1)
    s1 e1 v2 (Sail.Int.toNatChecked ((s2 -i e2))) 0))


/-- Type quantifiers: k_N : Nat, 1 ≤ (k_N - 1) -/
def CountLeadingSignBits (x : (BitVec k_N)) : Int :=
  (CountLeadingZeroBits
    ((Sail.BitVec.castWidth (m := (k_N - 1)) (Sail.BitVec.extractLsb x
        (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i 1))) 1)) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
        x (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i 2))) 0))))


def C27cEnsureDebugConfig (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (Havev8p9Debug ())) : Bool)
    then
      (do
        let w__1 ← (( do (HaveAArch32EL EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let limit : Nat :=
    if (w__2 : Bool)
    then 64
    else 16
  let w__3 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  if ((w__3 == (Neg.neg 1)) : Bool)
  then
    (do
      let w__4 ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 17) 2 limit))) )
        : SailM Nat )
      writeReg NUM_BREAKPOINTS (w__4 : Nat))
  else (pure (()))
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
         (pure (((w__5 ≥b 2) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
        (pure (((w__6 ≤b limit) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "sail-inputs/29-armcert-c27c.sail:60.58-60.59"
  let w__8 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  if ((w__8 == (Neg.neg 1)) : Bool)
  then
    (do
      let w__9 ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 18) 2 limit))) )
        : SailM Nat )
      writeReg NUM_WATCHPOINTS (w__9 : Nat))
  else (pure (()))
  let w__12 ← (( do
    if ((← do
         let w__10 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
         (pure (((w__10 ≥b 2) : Bool)))) : Bool)
    then
      (do
        let w__11 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
        (pure (((w__11 ≤b limit) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__12 "sail-inputs/29-armcert-c27c.sail:64.58-64.59"
  let breakpoints ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  ArmFull.assert ((breakpoints ≥b 2) && (breakpoints ≤b limit)) "sail-inputs/29-armcert-c27c.sail:66.50-66.51"
  let w__13 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
  if ((w__13 == (Neg.neg 1)) : Bool)
  then
    (do
      let w__14 ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 19) 1 breakpoints)))
        ) : SailM Nat )
      writeReg __num_ctx_breakpoints (w__14 : Nat))
  else (pure (()))
  let w__17 ← (( do
    if ((← do
         let w__15 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
         (pure (((w__15 ≥b 1) : Bool)))) : Bool)
    then
      (do
        let w__16 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
        (pure (((w__16 ≤b breakpoints) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__17 "sail-inputs/29-armcert-c27c.sail:70.76-70.77"


def __UNKNOWN_AccessDescriptor (_ : Unit) : SailM AccessDescriptor := do
  (undefined_AccessDescriptor (← occLabel 118) ())


def undefined_FaultRecord (ℓ : ChoiceLabel) (_ : Unit) : SailM FaultRecord := do
  let w__0 ← (( do (undefined_Fault (ℓ.child 0) ()) ) : SailM Fault )
  let w__1 ← (( do (undefined_AccessDescriptor (ℓ.child 1) ()) ) : SailM AccessDescriptor )
  let w__2 ← (( do (undefined_FullAddress (ℓ.child 2) ()) ) : SailM FullAddress )
  let w__3 ← (( do (undefined_GPCFRecord (ℓ.child 3) ()) ) : SailM GPCFRecord )
  let w__4 ← (( do (undefined_FullAddress (ℓ.child 4) ()) ) : SailM FullAddress )
  let w__5 ← (( do (undefined_bool_at (ℓ.child 5) ()) ) : SailM Bool )
  let w__6 ← (( do (undefined_bool_at (ℓ.child 6) ()) ) : SailM Bool )
  let w__7 ← (( do (undefined_bool_at (ℓ.child 7) ()) ) : SailM Bool )
  let w__8 ← (( do (undefined_bool_at (ℓ.child 8) ()) ) : SailM Bool )
  let w__9 ← (( do (undefined_bool_at (ℓ.child 9) ()) ) : SailM Bool )
  let w__10 ← (( do (undefined_int_at (ℓ.child 10) ()) ) : SailM Int )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 1) ) : SailM (BitVec 1) )
  let w__12 ← (( do (undefined_bool_at (ℓ.child 12) ()) ) : SailM Bool )
  let w__13 ← (( do (undefined_bool_at (ℓ.child 13) ()) ) : SailM Bool )
  let w__14 ← (( do (undefined_bool_at (ℓ.child 14) ()) ) : SailM Bool )
  let w__15 ← (( do (undefined_bool_at (ℓ.child 15) ()) ) : SailM Bool )
  let w__16 ← (( do (undefined_bool_at (ℓ.child 16) ()) ) : SailM Bool )
  let w__17 ← (( do (undefined_bitvector_at (ℓ.child 17) 4) ) : SailM (BitVec 4) )
  let w__18 ← (( do (undefined_ErrorState (ℓ.child 18) ()) ) : SailM ErrorState )
  let w__19 ← (( do (undefined_bitvector_at (ℓ.child 19) 4) ) : SailM (BitVec 4) )
  (pure ({ statuscode := w__0
           access := w__1
           ipaddress := w__2
           gpcf := w__3
           paddress := w__4
           gpcfs2walk := w__5
           s2fs1walk := w__6
           write := w__7
           s1tagnotdata := w__8
           tagaccess := w__9
           level := w__10
           extflag := w__11
           secondstage := w__12
           assuredonly := w__13
           toplevel := w__14
           overlay := w__15
           dirtybit := w__16
           domain := w__17
           merrorstate := w__18
           debugmoe := w__19 }))


def __UNKNOWN_TTWState (_ : Unit) : SailM TTWState := do
  (undefined_TTWState (← occLabel 287) ())


end ArmFull.Functions
