import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive signal where | LOW | HIGH
  deriving BEq, Inhabited, Repr
  open signal

inductive exception where
  | Error_Undefined (_ : Unit)
  | Error_See (_ : String)
  | Error_ImplementationDefined (_ : String)
  | Error_ReservedEncoding (_ : Unit)
  | Error_ExceptionTaken (_ : Unit)
  | Error_Unpredictable (_ : Unit)
  | Error_ConstrainedUnpredictable (_ : Unit)
  | Error_SError (_ : Bool)
  deriving Inhabited, BEq, Repr
  open exception

abbrev is_VL (k_vl : Int) : Bool := List.elem k_vl [128, 256, 512, 1024, 2048]

abbrev is_PL (k_pl : Int) : Bool := List.elem k_pl [16, 32, 64, 128, 256]

abbrev vector_length := Int

abbrev predicate_length := Int

abbrev Configuration_Type := (BitVec 32)

abbrev ACCDATA_EL1_Type := (BitVec 64)

abbrev AMCFGR_EL0_Type := (BitVec 64)

abbrev AMCFGR_Type := (BitVec 32)

abbrev AMCG1IDR_EL0_Type := (BitVec 64)

abbrev AMCGCR_EL0_Type := (BitVec 64)

abbrev AMCGCR_Type := (BitVec 32)

abbrev AMCIDR0_Type := (BitVec 32)

abbrev AMCIDR1_Type := (BitVec 32)

abbrev AMCIDR2_Type := (BitVec 32)

abbrev AMCIDR3_Type := (BitVec 32)

abbrev AMCNTENCLR0_EL0_Type := (BitVec 64)

abbrev AMCNTENCLR0_Type := (BitVec 32)

abbrev AMCNTENCLR1_EL0_Type := (BitVec 64)

abbrev AMCNTENCLR1_Type := (BitVec 32)

abbrev AMCNTENSET0_EL0_Type := (BitVec 64)

abbrev AMCNTENSET0_Type := (BitVec 32)

abbrev AMCNTENSET1_EL0_Type := (BitVec 64)

abbrev AMCNTENSET1_Type := (BitVec 32)

abbrev AMCR_EL0_Type := (BitVec 64)

abbrev AMCR_Type := (BitVec 32)

abbrev AMDEVARCH_Type := (BitVec 32)

abbrev AMDEVTYPE_Type := (BitVec 32)

abbrev AMEVCNTR0_EL0_Type := (BitVec 64)

abbrev AMEVCNTR0_Type := (BitVec 64)

abbrev AMEVCNTR1_EL0_Type := (BitVec 64)

abbrev AMEVCNTR1_Type := (BitVec 64)

abbrev AMEVTYPER0_EL0_Type := (BitVec 64)

abbrev AMEVTYPER0_Type := (BitVec 32)

abbrev AMEVTYPER1_EL0_Type := (BitVec 64)

abbrev AMEVTYPER1_Type := (BitVec 32)

abbrev AMIIDR_Type := (BitVec 32)

abbrev AMPIDR0_Type := (BitVec 32)

abbrev AMPIDR1_Type := (BitVec 32)

abbrev AMPIDR2_Type := (BitVec 32)

abbrev AMPIDR3_Type := (BitVec 32)

abbrev AMPIDR4_Type := (BitVec 32)

abbrev AMUSERENR_EL0_Type := (BitVec 64)

abbrev AMUSERENR_Type := (BitVec 32)

abbrev BRBCR_EL1_Type := (BitVec 64)

abbrev BRBCR_EL2_Type := (BitVec 64)

abbrev BRBFCR_EL1_Type := (BitVec 64)

abbrev BRBIDR0_EL1_Type := (BitVec 64)

abbrev BRBINFINJ_EL1_Type := (BitVec 64)

abbrev BRBINFType := (BitVec 64)

abbrev BRBINF_EL1_Type := (BitVec 64)

abbrev BRBSRCINJ_EL1_Type := (BitVec 64)

abbrev BRBSRCType := (BitVec 64)

abbrev BRBSRC_EL1_Type := (BitVec 64)

abbrev BRBTGTINJ_EL1_Type := (BitVec 64)

abbrev BRBTGTType := (BitVec 64)

abbrev BRBTGT_EL1_Type := (BitVec 64)

abbrev BRBTS_EL1_Type := (BitVec 64)

abbrev CCSIDR2_EL1_Type := (BitVec 64)

abbrev CCSIDR2_Type := (BitVec 32)

abbrev CCSIDR_EL1_Type := (BitVec 64)

abbrev CCSIDR_Type := (BitVec 32)

abbrev CLIDR_EL1_Type := (BitVec 64)

abbrev CLIDR_Type := (BitVec 32)

abbrev CNTCR_Type := (BitVec 32)

abbrev CNTEL0ACR_Type := (BitVec 32)

abbrev CNTFID0_Type := (BitVec 32)

abbrev CNTHCTL_EL2_Type := (BitVec 64)

abbrev CNTHCTL_Type := (BitVec 32)

abbrev CNTHPS_CTL_EL2_Type := (BitVec 64)

abbrev CNTHPS_CTL_Type := (BitVec 32)

abbrev CNTHPS_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHPS_TVAL_EL2_Type := (BitVec 64)

abbrev CNTHP_CTL_EL2_Type := (BitVec 64)

abbrev CNTHP_CTL_Type := (BitVec 32)

abbrev CNTHP_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHP_CVAL_Type := (BitVec 64)

abbrev CNTHP_TVAL_EL2_Type := (BitVec 64)

abbrev CNTHVS_CTL_EL2_Type := (BitVec 64)

abbrev CNTHVS_CTL_Type := (BitVec 32)

abbrev CNTHVS_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHVS_TVAL_EL2_Type := (BitVec 64)

abbrev CNTHV_CTL_EL2_Type := (BitVec 64)

abbrev CNTHV_CTL_Type := (BitVec 32)

abbrev CNTHV_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHV_TVAL_EL2_Type := (BitVec 64)

abbrev CNTID_Type := (BitVec 32)

abbrev CNTKCTL_EL1_Type := (BitVec 64)

abbrev CNTKCTL_Type := (BitVec 32)

abbrev CNTNSAR_Type := (BitVec 32)

abbrev CNTPS_CTL_EL1_Type := (BitVec 64)

abbrev CNTPS_CVAL_EL1_Type := (BitVec 64)

abbrev CNTPS_TVAL_EL1_Type := (BitVec 64)

abbrev CNTP_CTL_EL0_Type := (BitVec 64)

abbrev CNTP_CTL_Type := (BitVec 32)

abbrev CNTP_CVAL_EL0_Type := (BitVec 64)

abbrev CNTP_CVAL_Type := (BitVec 64)

abbrev CNTP_TVAL_EL0_Type := (BitVec 64)

abbrev CNTSCR_Type := (BitVec 32)

abbrev CNTSR_Type := (BitVec 32)

abbrev CNTV_CTL_EL0_Type := (BitVec 64)

abbrev CNTV_CTL_Type := (BitVec 32)

abbrev CNTV_CVAL_EL0_Type := (BitVec 64)

abbrev CNTV_CVAL_Type := (BitVec 64)

abbrev CNTV_TVAL_EL0_Type := (BitVec 64)

abbrev CONTEXTIDR_EL1_Type := (BitVec 64)

abbrev CONTEXTIDR_EL2_Type := (BitVec 64)

abbrev CONTEXTIDR_Type := (BitVec 32)

abbrev CPACR_EL1_Type := (BitVec 64)

abbrev CPACR_Type := (BitVec 32)

abbrev CPTR_EL2_Type := (BitVec 64)

abbrev CPTR_EL3_Type := (BitVec 64)

abbrev CSSELR_EL1_Type := (BitVec 64)

abbrev CSSELR_Type := (BitVec 32)

abbrev CTIAUTHSTATUS_Type := (BitVec 32)

abbrev CTICIDR0_Type := (BitVec 32)

abbrev CTICIDR1_Type := (BitVec 32)

abbrev CTICIDR2_Type := (BitVec 32)

abbrev CTICIDR3_Type := (BitVec 32)

abbrev CTICONTROL_Type := (BitVec 32)

abbrev CTIDEVARCH_Type := (BitVec 32)

abbrev CTIDEVCTL_Type := (BitVec 32)

abbrev CTIDEVID_Type := (BitVec 32)

abbrev CTIDEVTYPE_Type := (BitVec 32)

abbrev CTIITCTRL_Type := (BitVec 32)

abbrev CTILAR_Type := (BitVec 32)

abbrev CTILSR_Type := (BitVec 32)

abbrev CTIPIDR0_Type := (BitVec 32)

abbrev CTIPIDR1_Type := (BitVec 32)

abbrev CTIPIDR2_Type := (BitVec 32)

abbrev CTIPIDR3_Type := (BitVec 32)

abbrev CTIPIDR4_Type := (BitVec 32)

abbrev CTR_EL0_Type := (BitVec 64)

abbrev CTR_Type := (BitVec 32)

abbrev DACR32_EL2_Type := (BitVec 64)

abbrev DACR_Type := (BitVec 32)

abbrev DBGAUTHSTATUS_EL1_Type := (BitVec 64)

abbrev DBGAUTHSTATUS_Type := (BitVec 32)

abbrev DBGBCR_EL1_Type := (BitVec 64)

abbrev DBGBCR_Type := (BitVec 32)

abbrev DBGBVR_EL1_Type := (BitVec 64)

abbrev DBGBVR_Type := (BitVec 32)

abbrev DBGBXVR_Type := (BitVec 32)

abbrev DBGCLAIMCLR_EL1_Type := (BitVec 64)

abbrev DBGCLAIMCLR_Type := (BitVec 32)

abbrev DBGCLAIMSET_EL1_Type := (BitVec 64)

abbrev DBGCLAIMSET_Type := (BitVec 32)

abbrev DBGDCCINT_Type := (BitVec 32)

abbrev DBGDEVID1_Type := (BitVec 32)

abbrev DBGDEVID_Type := (BitVec 32)

abbrev DBGDIDR_Type := (BitVec 32)

abbrev DBGDRAR_Type := (BitVec 64)

abbrev DBGDSCRext_Type := (BitVec 32)

abbrev DBGDSCRint_Type := (BitVec 32)

abbrev DBGDTRRXext_Type := (BitVec 32)

abbrev DBGDTRRXint_Type := (BitVec 32)

abbrev DBGDTRTXext_Type := (BitVec 32)

abbrev DBGDTRTXint_Type := (BitVec 32)

abbrev DBGDTR_EL0_Type := (BitVec 64)

abbrev DBGOSDLR_Type := (BitVec 32)

abbrev DBGOSECCR_Type := (BitVec 32)

abbrev DBGOSLAR_Type := (BitVec 32)

abbrev DBGOSLSR_Type := (BitVec 32)

abbrev DBGPRCR_EL1_Type := (BitVec 64)

abbrev DBGPRCR_Type := (BitVec 32)

abbrev DBGVCR32_EL2_Type := (BitVec 64)

abbrev DBGVCR_Type := (BitVec 32)

abbrev DBGWCR_EL1_Type := (BitVec 64)

abbrev DBGWCR_Type := (BitVec 32)

abbrev DBGWVR_EL1_Type := (BitVec 64)

abbrev DBGWVR_Type := (BitVec 32)

abbrev DCZID_EL0_Type := (BitVec 64)

abbrev DFSR_Type := (BitVec 32)

abbrev DISR_EL1_Type := (BitVec 64)

abbrev DISR_Type := (BitVec 32)

abbrev DSPSR2_Type := (BitVec 32)

abbrev DSPSR_EL0_Type := (BitVec 64)

abbrev DSPSR_Type := (BitVec 32)

abbrev DormantCtl_Type := (BitVec 32)

abbrev EDAA32PFR_Type := (BitVec 64)

abbrev EDCIDR0_Type := (BitVec 32)

abbrev EDCIDR1_Type := (BitVec 32)

abbrev EDCIDR2_Type := (BitVec 32)

abbrev EDCIDR3_Type := (BitVec 32)

abbrev EDDEVARCH_Type := (BitVec 32)

abbrev EDDEVID1_Type := (BitVec 32)

abbrev EDDEVID_Type := (BitVec 32)

abbrev EDDEVTYPE_Type := (BitVec 32)

abbrev EDDFR1_Type := (BitVec 64)

abbrev EDDFR_Type := (BitVec 64)

abbrev EDECCR_Type := (BitVec 32)

abbrev EDECR_Type := (BitVec 32)

abbrev EDESR_Type := (BitVec 32)

abbrev EDHSR_Type := (BitVec 64)

abbrev EDITCTRL_Type := (BitVec 32)

abbrev EDLAR_Type := (BitVec 32)

abbrev EDLSR_Type := (BitVec 32)

abbrev EDPCSR_Type := (BitVec 64)

abbrev EDPFR_Type := (BitVec 64)

abbrev EDPIDR0_Type := (BitVec 32)

abbrev EDPIDR1_Type := (BitVec 32)

abbrev EDPIDR2_Type := (BitVec 32)

abbrev EDPIDR3_Type := (BitVec 32)

abbrev EDPIDR4_Type := (BitVec 32)

abbrev EDPRCR_Type := (BitVec 32)

abbrev EDPRSR_Type := (BitVec 32)

abbrev EDRCR_Type := (BitVec 32)

abbrev EDSCR2_Type := (BitVec 32)

abbrev EDSCR_Type := (BitVec 32)

abbrev EDVIDSR_Type := (BitVec 32)

abbrev ERRIDR_EL1_Type := (BitVec 64)

abbrev ERRIDR_Type := (BitVec 32)

abbrev ERRSELR_EL1_Type := (BitVec 64)

abbrev ERRSELR_Type := (BitVec 32)

abbrev ERRnFR_ElemType := (BitVec 64)

abbrev ERXGSR_EL1_Type := (BitVec 64)

abbrev ESRType := (BitVec 64)

abbrev ESR_EL1_Type := (BitVec 64)

abbrev ESR_EL2_Type := (BitVec 64)

abbrev ESR_EL3_Type := (BitVec 64)

abbrev FPCRType := (BitVec 64)

abbrev FPCR_Type := (BitVec 64)

abbrev FPEXC32_EL2_Type := (BitVec 64)

abbrev FPEXC_Type := (BitVec 32)

abbrev FPSCR_Type := (BitVec 32)

abbrev FPSID_Type := (BitVec 32)

abbrev FPSR_Type := (BitVec 64)

abbrev GCR_EL1_Type := (BitVec 64)

abbrev GCSCRE0_EL1_Type := (BitVec 64)

abbrev GCSCR_EL1_Type := (BitVec 64)

abbrev GCSCR_EL2_Type := (BitVec 64)

abbrev GCSCR_EL3_Type := (BitVec 64)

abbrev GCSPR_EL0_Type := (BitVec 64)

abbrev GCSPR_EL1_Type := (BitVec 64)

abbrev GCSPR_EL2_Type := (BitVec 64)

abbrev GCSPR_EL3_Type := (BitVec 64)

abbrev GICC_ABPR_Type := (BitVec 32)

abbrev GICC_AEOIR_Type := (BitVec 32)

abbrev GICC_AHPPIR_Type := (BitVec 32)

abbrev GICC_AIAR_Type := (BitVec 32)

abbrev GICC_BPR_Type := (BitVec 32)

abbrev GICC_CTLR_Type := (BitVec 32)

abbrev GICC_DIR_Type := (BitVec 32)

abbrev GICC_EOIR_Type := (BitVec 32)

abbrev GICC_HPPIR_Type := (BitVec 32)

abbrev GICC_IAR_Type := (BitVec 32)

abbrev GICC_PMR_Type := (BitVec 32)

abbrev GICC_RPR_Type := (BitVec 32)

abbrev GICC_STATUSR_Type := (BitVec 32)

abbrev GICD_CLRSPI_NSR_Type := (BitVec 32)

abbrev GICD_CLRSPI_SR_Type := (BitVec 32)

abbrev GICD_CTLR_Type := (BitVec 32)

abbrev GICD_IIDR_Type := (BitVec 32)

abbrev GICD_SETSPI_NSR_Type := (BitVec 32)

abbrev GICD_SETSPI_SR_Type := (BitVec 32)

abbrev GICD_SGIR_Type := (BitVec 32)

abbrev GICD_STATUSR_Type := (BitVec 32)

abbrev GICD_TYPER2_Type := (BitVec 32)

abbrev GICD_TYPER_Type := (BitVec 32)

abbrev GICH_EISR_Type := (BitVec 32)

abbrev GICH_ELRSR_Type := (BitVec 32)

abbrev GICH_HCR_Type := (BitVec 32)

abbrev GICH_MISR_Type := (BitVec 32)

abbrev GICH_VMCR_Type := (BitVec 32)

abbrev GICH_VTR_Type := (BitVec 32)

abbrev GICM_CLRSPI_NSR_Type := (BitVec 32)

abbrev GICM_CLRSPI_SR_Type := (BitVec 32)

abbrev GICM_IIDR_Type := (BitVec 32)

abbrev GICM_SETSPI_NSR_Type := (BitVec 32)

abbrev GICM_SETSPI_SR_Type := (BitVec 32)

abbrev GICM_TYPER_Type := (BitVec 32)

abbrev GICR_CLRLPIR_Type := (BitVec 64)

abbrev GICR_CTLR_Type := (BitVec 32)

abbrev GICR_IIDR_Type := (BitVec 32)

abbrev GICR_INMIR0_Type := (BitVec 32)

abbrev GICR_INVALLR_Type := (BitVec 64)

abbrev GICR_INVLPIR_Type := (BitVec 64)

abbrev GICR_ISENABLER0_Type := (BitVec 32)

abbrev GICR_MPAMIDR_Type := (BitVec 32)

abbrev GICR_PARTIDR_Type := (BitVec 32)

abbrev GICR_PENDBASER_Type := (BitVec 64)

abbrev GICR_PROPBASER_Type := (BitVec 64)

abbrev GICR_SETLPIR_Type := (BitVec 64)

abbrev GICR_STATUSR_Type := (BitVec 32)

abbrev GICR_SYNCR_Type := (BitVec 32)

abbrev GICR_VPENDBASER_Type := (BitVec 64)

abbrev GICR_VPROPBASER_Type := (BitVec 64)

abbrev GICR_VSGIPENDR_Type := (BitVec 32)

abbrev GICR_VSGIR_Type := (BitVec 32)

abbrev GICR_WAKER_Type := (BitVec 32)

abbrev GICV_ABPR_Type := (BitVec 32)

abbrev GICV_AEOIR_Type := (BitVec 32)

abbrev GICV_AHPPIR_Type := (BitVec 32)

abbrev GICV_AIAR_Type := (BitVec 32)

abbrev GICV_BPR_Type := (BitVec 32)

abbrev GICV_CTLR_Type := (BitVec 32)

abbrev GICV_DIR_Type := (BitVec 32)

abbrev GICV_EOIR_Type := (BitVec 32)

abbrev GICV_HPPIR_Type := (BitVec 32)

abbrev GICV_IAR_Type := (BitVec 32)

abbrev GICV_PMR_Type := (BitVec 32)

abbrev GICV_RPR_Type := (BitVec 32)

abbrev GICV_STATUSR_Type := (BitVec 32)

abbrev GITS_CBASER_Type := (BitVec 64)

abbrev GITS_CREADR_Type := (BitVec 64)

abbrev GITS_CTLR_Type := (BitVec 32)

abbrev GITS_CWRITER_Type := (BitVec 64)

abbrev GITS_IIDR_Type := (BitVec 32)

abbrev GITS_MPAMIDR_Type := (BitVec 32)

abbrev GITS_MPIDR_Type := (BitVec 32)

abbrev GITS_PARTIDR_Type := (BitVec 32)

abbrev GITS_SGIR_Type := (BitVec 64)

abbrev GITS_STATUSR_Type := (BitVec 32)

abbrev GITS_TYPER_Type := (BitVec 64)

abbrev GMID_EL1_Type := (BitVec 64)

abbrev GPCCR_EL3_Type := (BitVec 64)

abbrev GPTBR_EL3_Type := (BitVec 64)

abbrev HAFGRTR_EL2_Type := (BitVec 64)

abbrev HCPTR_Type := (BitVec 32)

abbrev HCR2_Type := (BitVec 32)

abbrev HCRX_EL2_Type := (BitVec 64)

abbrev HCR_EL2_Type := (BitVec 64)

abbrev HCR_Type := (BitVec 32)

abbrev HDCR_Type := (BitVec 32)

abbrev HDFGRTR2_EL2_Type := (BitVec 64)

abbrev HDFGRTR_EL2_Type := (BitVec 64)

abbrev HDFGWTR2_EL2_Type := (BitVec 64)

abbrev HDFGWTR_EL2_Type := (BitVec 64)

abbrev HFGITR_EL2_Type := (BitVec 64)

abbrev HFGRTR2_EL2_Type := (BitVec 64)

abbrev HFGRTR_EL2_Type := (BitVec 64)

abbrev HFGWTR2_EL2_Type := (BitVec 64)

abbrev HFGWTR_EL2_Type := (BitVec 64)

abbrev HMAIR0_Type := (BitVec 32)

abbrev HMAIR1_Type := (BitVec 32)

abbrev HPFAR_EL2_Type := (BitVec 64)

abbrev HPFAR_Type := (BitVec 32)

abbrev HRMR_Type := (BitVec 32)

abbrev HSCTLR_Type := (BitVec 32)

abbrev HSR_Type := (BitVec 32)

abbrev HSTR_EL2_Type := (BitVec 64)

abbrev HSTR_Type := (BitVec 32)

abbrev HTCR_Type := (BitVec 32)

abbrev HTRFCR_Type := (BitVec 32)

abbrev HTTBR_Type := (BitVec 64)

abbrev ICC_AP1R_EL1_Type := (BitVec 64)

abbrev ICC_ASGI1R_EL1_Type := (BitVec 64)

abbrev ICC_ASGI1R_Type := (BitVec 64)

abbrev ICC_BPR0_EL1_Type := (BitVec 64)

abbrev ICC_BPR0_Type := (BitVec 32)

abbrev ICC_BPR1_EL1_Type := (BitVec 64)

abbrev ICC_BPR1_Type := (BitVec 32)

abbrev ICC_CTLR_EL1_Type := (BitVec 64)

abbrev ICC_CTLR_EL3_Type := (BitVec 64)

abbrev ICC_CTLR_Type := (BitVec 32)

abbrev ICC_DIR_EL1_Type := (BitVec 64)

abbrev ICC_DIR_Type := (BitVec 32)

abbrev ICC_EOIR0_EL1_Type := (BitVec 64)

abbrev ICC_EOIR0_Type := (BitVec 32)

abbrev ICC_EOIR1_EL1_Type := (BitVec 64)

abbrev ICC_EOIR1_Type := (BitVec 32)

abbrev ICC_HPPIR0_EL1_Type := (BitVec 64)

abbrev ICC_HPPIR0_Type := (BitVec 32)

abbrev ICC_HPPIR1_EL1_Type := (BitVec 64)

abbrev ICC_HPPIR1_Type := (BitVec 32)

abbrev ICC_HSRE_Type := (BitVec 32)

abbrev ICC_IAR0_EL1_Type := (BitVec 64)

abbrev ICC_IAR0_Type := (BitVec 32)

abbrev ICC_IAR1_EL1_Type := (BitVec 64)

abbrev ICC_IAR1_Type := (BitVec 32)

abbrev ICC_IGRPEN0_EL1_Type := (BitVec 64)

abbrev ICC_IGRPEN0_Type := (BitVec 32)

abbrev ICC_IGRPEN1_EL1_Type := (BitVec 64)

abbrev ICC_IGRPEN1_EL3_Type := (BitVec 64)

abbrev ICC_IGRPEN1_Type := (BitVec 32)

abbrev ICC_MCTLR_Type := (BitVec 32)

abbrev ICC_MGRPEN1_Type := (BitVec 32)

abbrev ICC_MSRE_Type := (BitVec 32)

abbrev ICC_NMIAR1_EL1_Type := (BitVec 64)

abbrev ICC_PMR_EL1_Type := (BitVec 64)

abbrev ICC_PMR_Type := (BitVec 32)

abbrev ICC_RPR_EL1_Type := (BitVec 64)

abbrev ICC_RPR_Type := (BitVec 32)

abbrev ICC_SGI0R_EL1_Type := (BitVec 64)

abbrev ICC_SGI0R_Type := (BitVec 64)

abbrev ICC_SGI1R_EL1_Type := (BitVec 64)

abbrev ICC_SGI1R_Type := (BitVec 64)

abbrev ICC_SRE_EL1_Type := (BitVec 64)

abbrev ICC_SRE_EL2_Type := (BitVec 64)

abbrev ICC_SRE_EL3_Type := (BitVec 64)

abbrev ICC_SRE_Type := (BitVec 32)

abbrev ICH_AP0R_EL2_Type := (BitVec 64)

abbrev ICH_AP0R_Type := (BitVec 32)

abbrev ICH_AP1R_EL2_Type := (BitVec 64)

abbrev ICH_AP1R_Type := (BitVec 32)

abbrev ICH_EISR_EL2_Type := (BitVec 64)

abbrev ICH_EISR_Type := (BitVec 32)

abbrev ICH_ELRSR_EL2_Type := (BitVec 64)

abbrev ICH_ELRSR_Type := (BitVec 32)

abbrev ICH_HCR_EL2_Type := (BitVec 64)

abbrev ICH_HCR_Type := (BitVec 32)

abbrev ICH_LRC_Type := (BitVec 32)

abbrev ICH_LR_EL2_Type := (BitVec 64)

abbrev ICH_LR_Type := (BitVec 32)

abbrev ICH_MISR_EL2_Type := (BitVec 64)

abbrev ICH_MISR_Type := (BitVec 32)

abbrev ICH_VMCR_EL2_Type := (BitVec 64)

abbrev ICH_VMCR_Type := (BitVec 32)

abbrev ICH_VTR_EL2_Type := (BitVec 64)

abbrev ICH_VTR_Type := (BitVec 32)

abbrev ICV_AP1R_EL1_Type := (BitVec 64)

abbrev ICV_BPR0_EL1_Type := (BitVec 64)

abbrev ICV_BPR0_Type := (BitVec 32)

abbrev ICV_BPR1_EL1_Type := (BitVec 64)

abbrev ICV_BPR1_Type := (BitVec 32)

abbrev ICV_CTLR_EL1_Type := (BitVec 64)

abbrev ICV_CTLR_Type := (BitVec 32)

abbrev ICV_DIR_EL1_Type := (BitVec 64)

abbrev ICV_DIR_Type := (BitVec 32)

abbrev ICV_EOIR0_EL1_Type := (BitVec 64)

abbrev ICV_EOIR0_Type := (BitVec 32)

abbrev ICV_EOIR1_EL1_Type := (BitVec 64)

abbrev ICV_EOIR1_Type := (BitVec 32)

abbrev ICV_HPPIR0_EL1_Type := (BitVec 64)

abbrev ICV_HPPIR0_Type := (BitVec 32)

abbrev ICV_HPPIR1_EL1_Type := (BitVec 64)

abbrev ICV_HPPIR1_Type := (BitVec 32)

abbrev ICV_IAR0_EL1_Type := (BitVec 64)

abbrev ICV_IAR0_Type := (BitVec 32)

abbrev ICV_IAR1_EL1_Type := (BitVec 64)

abbrev ICV_IAR1_Type := (BitVec 32)

abbrev ICV_IGRPEN0_EL1_Type := (BitVec 64)

abbrev ICV_IGRPEN0_Type := (BitVec 32)

abbrev ICV_IGRPEN1_EL1_Type := (BitVec 64)

abbrev ICV_IGRPEN1_Type := (BitVec 32)

abbrev ICV_NMIAR1_EL1_Type := (BitVec 64)

abbrev ICV_PMR_EL1_Type := (BitVec 64)

abbrev ICV_PMR_Type := (BitVec 32)

abbrev ICV_RPR_EL1_Type := (BitVec 64)

abbrev ICV_RPR_Type := (BitVec 32)

abbrev ID_AA64DFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64DFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64ISAR0_EL1_Type := (BitVec 64)

abbrev ID_AA64ISAR1_EL1_Type := (BitVec 64)

abbrev ID_AA64ISAR2_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR2_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR3_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR4_EL1_Type := (BitVec 64)

abbrev ID_AA64PFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64PFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64PFR2_EL1_Type := (BitVec 64)

abbrev ID_AA64SMFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64ZFR0_EL1_Type := (BitVec 64)

abbrev ID_DFR0_EL1_Type := (BitVec 64)

abbrev ID_DFR0_Type := (BitVec 32)

abbrev ID_DFR1_EL1_Type := (BitVec 64)

abbrev ID_DFR1_Type := (BitVec 32)

abbrev ID_ISAR0_EL1_Type := (BitVec 64)

abbrev ID_ISAR0_Type := (BitVec 32)

abbrev ID_ISAR1_EL1_Type := (BitVec 64)

abbrev ID_ISAR1_Type := (BitVec 32)

abbrev ID_ISAR2_EL1_Type := (BitVec 64)

abbrev ID_ISAR2_Type := (BitVec 32)

abbrev ID_ISAR3_EL1_Type := (BitVec 64)

abbrev ID_ISAR3_Type := (BitVec 32)

abbrev ID_ISAR4_EL1_Type := (BitVec 64)

abbrev ID_ISAR4_Type := (BitVec 32)

abbrev ID_ISAR5_EL1_Type := (BitVec 64)

abbrev ID_ISAR5_Type := (BitVec 32)

abbrev ID_ISAR6_EL1_Type := (BitVec 64)

abbrev ID_ISAR6_Type := (BitVec 32)

abbrev ID_MMFR0_EL1_Type := (BitVec 64)

abbrev ID_MMFR0_Type := (BitVec 32)

abbrev ID_MMFR1_EL1_Type := (BitVec 64)

abbrev ID_MMFR1_Type := (BitVec 32)

abbrev ID_MMFR2_EL1_Type := (BitVec 64)

abbrev ID_MMFR2_Type := (BitVec 32)

abbrev ID_MMFR3_EL1_Type := (BitVec 64)

abbrev ID_MMFR3_Type := (BitVec 32)

abbrev ID_MMFR4_EL1_Type := (BitVec 64)

abbrev ID_MMFR4_Type := (BitVec 32)

abbrev ID_MMFR5_EL1_Type := (BitVec 64)

abbrev ID_MMFR5_Type := (BitVec 32)

abbrev ID_PFR0_EL1_Type := (BitVec 64)

abbrev ID_PFR0_Type := (BitVec 32)

abbrev ID_PFR1_EL1_Type := (BitVec 64)

abbrev ID_PFR1_Type := (BitVec 32)

abbrev ID_PFR2_EL1_Type := (BitVec 64)

abbrev ID_PFR2_Type := (BitVec 32)

abbrev IFSR32_EL2_Type := (BitVec 64)

abbrev IFSR_Type := (BitVec 32)

abbrev ISR_EL1_Type := (BitVec 64)

abbrev ISR_Type := (BitVec 32)

abbrev LORC_EL1_Type := (BitVec 64)

abbrev LOREA_EL1_Type := (BitVec 64)

abbrev LORID_EL1_Type := (BitVec 64)

abbrev LORN_EL1_Type := (BitVec 64)

abbrev LORSA_EL1_Type := (BitVec 64)

abbrev MAIR0_Type := (BitVec 32)

abbrev MAIR1_Type := (BitVec 32)

abbrev MAIR2_EL1_Type := (BitVec 64)

abbrev MAIR2_EL2_Type := (BitVec 64)

abbrev MAIR2_EL3_Type := (BitVec 64)

abbrev MAIRType := (BitVec 64)

abbrev MAIR_EL1_Type := (BitVec 64)

abbrev MAIR_EL2_Type := (BitVec 64)

abbrev MAIR_EL3_Type := (BitVec 64)

abbrev MDCCINT_EL1_Type := (BitVec 64)

abbrev MDCCSR_EL0_Type := (BitVec 64)

abbrev MDCR_EL2_Type := (BitVec 64)

abbrev MDCR_EL3_Type := (BitVec 64)

abbrev MDRAR_EL1_Type := (BitVec 64)

abbrev MDSCR_EL1_Type := (BitVec 64)

abbrev MDSELR_EL1_Type := (BitVec 64)

abbrev MECIDR_EL2_Type := (BitVec 64)

abbrev MECID_A0_EL2_Type := (BitVec 64)

abbrev MECID_A1_EL2_Type := (BitVec 64)

abbrev MECID_P0_EL2_Type := (BitVec 64)

abbrev MECID_P1_EL2_Type := (BitVec 64)

abbrev MECID_RL_A_EL3_Type := (BitVec 64)

abbrev MFAR_EL3_Type := (BitVec 64)

abbrev MIDR_EL1_Type := (BitVec 64)

abbrev MIDR_Type := (BitVec 32)

abbrev MPAM0_EL1_Type := (BitVec 64)

abbrev MPAM1_EL1_Type := (BitVec 64)

abbrev MPAM2_EL2_Type := (BitVec 64)

abbrev MPAM3_EL3_Type := (BitVec 64)

abbrev MPAMHCR_EL2_Type := (BitVec 64)

abbrev MPAMIDR_EL1_Type := (BitVec 64)

abbrev MPAMSM_EL1_Type := (BitVec 64)

abbrev MPAMVPM0_EL2_Type := (BitVec 64)

abbrev MPAMVPM1_EL2_Type := (BitVec 64)

abbrev MPAMVPM2_EL2_Type := (BitVec 64)

abbrev MPAMVPM3_EL2_Type := (BitVec 64)

abbrev MPAMVPM4_EL2_Type := (BitVec 64)

abbrev MPAMVPM5_EL2_Type := (BitVec 64)

abbrev MPAMVPM6_EL2_Type := (BitVec 64)

abbrev MPAMVPM7_EL2_Type := (BitVec 64)

abbrev MPAMVPMV_EL2_Type := (BitVec 64)

abbrev MPIDR_EL1_Type := (BitVec 64)

abbrev MPIDR_Type := (BitVec 32)

abbrev MVBAR_Type := (BitVec 32)

abbrev MVFR0_EL1_Type := (BitVec 64)

abbrev MVFR0_Type := (BitVec 32)

abbrev MVFR1_EL1_Type := (BitVec 64)

abbrev MVFR1_Type := (BitVec 32)

abbrev MVFR2_EL1_Type := (BitVec 64)

abbrev MVFR2_Type := (BitVec 32)

abbrev NMRR_Type := (BitVec 32)

abbrev NSACR_Type := (BitVec 32)

abbrev OSDLR_EL1_Type := (BitVec 64)

abbrev OSECCR_EL1_Type := (BitVec 64)

abbrev OSLAR_EL1_Type := (BitVec 64)

abbrev OSLSR_EL1_Type := (BitVec 64)

abbrev PAR_EL1_Type := (BitVec 128)

abbrev PAR_Type := (BitVec 64)

abbrev PFAR_EL1_Type := (BitVec 64)

abbrev PFAR_EL2_Type := (BitVec 64)

abbrev PIRE0_EL1_Type := (BitVec 64)

abbrev PIRE0_EL2_Type := (BitVec 64)

abbrev PIR_EL1_Type := (BitVec 64)

abbrev PIR_EL2_Type := (BitVec 64)

abbrev PIR_EL3_Type := (BitVec 64)

abbrev PMAUTHSTATUS_Type := (BitVec 32)

abbrev PMBIDR_EL1_Type := (BitVec 64)

abbrev PMBLIMITR_EL1_Type := (BitVec 64)

abbrev PMBPTR_EL1_Type := (BitVec 64)

abbrev PMBSR_EL1_Type := (BitVec 64)

abbrev PMCCFILTR_EL0_Type := (BitVec 64)

abbrev PMCCFILTR_Type := (BitVec 32)

abbrev PMCCNTR_EL0_Type := (BitVec 64)

abbrev PMCCNTR_Type := (BitVec 64)

abbrev PMCCNTSVR_EL1_Type := (BitVec 64)

abbrev PMCEID0_EL0_Type := (BitVec 64)

abbrev PMCEID0_Type := (BitVec 32)

abbrev PMCEID1_EL0_Type := (BitVec 64)

abbrev PMCEID1_Type := (BitVec 32)

abbrev PMCEID2_Type := (BitVec 32)

abbrev PMCEID3_Type := (BitVec 32)

abbrev PMCFGR_Type := (BitVec 64)

abbrev PMCGCR0_Type := (BitVec 32)

abbrev PMCIDR0_Type := (BitVec 32)

abbrev PMCIDR1_Type := (BitVec 32)

abbrev PMCIDR2_Type := (BitVec 32)

abbrev PMCIDR3_Type := (BitVec 32)

abbrev PMCNTENCLR_EL0_Type := (BitVec 64)

abbrev PMCNTENCLR_Type := (BitVec 32)

abbrev PMCNTENSET_EL0_Type := (BitVec 64)

abbrev PMCNTENSET_Type := (BitVec 32)

abbrev PMCNTEN_Type := (BitVec 64)

abbrev PMCR_EL0_Type := (BitVec 64)

abbrev PMCR_Type := (BitVec 32)

abbrev PMDEVID_Type := (BitVec 32)

abbrev PMDEVTYPE_Type := (BitVec 32)

abbrev PMECR_EL1_Type := (BitVec 64)

abbrev PMEVCNTSVR_EL1_Type := (BitVec 64)

abbrev PMEVTYPER_EL0_Type := (BitVec 64)

abbrev PMEVTYPER_Type := (BitVec 32)

abbrev PMIAR_EL1_Type := (BitVec 64)

abbrev PMICFILTR_EL0_Type := (BitVec 64)

abbrev PMICNTR_EL0_Type := (BitVec 64)

abbrev PMICNTSVR_EL1_Type := (BitVec 64)

abbrev PMIIDR_Type := (BitVec 64)

abbrev PMINTENCLR_EL1_Type := (BitVec 64)

abbrev PMINTENCLR_Type := (BitVec 32)

abbrev PMINTENSET_EL1_Type := (BitVec 64)

abbrev PMINTENSET_Type := (BitVec 32)

abbrev PMINTEN_Type := (BitVec 64)

abbrev PMITCTRL_Type := (BitVec 32)

abbrev PMLAR_Type := (BitVec 32)

abbrev PMLSR_Type := (BitVec 32)

abbrev PMMIR_EL1_Type := (BitVec 64)

abbrev PMMIR_Type := (BitVec 32)

abbrev PMOVSCLR_EL0_Type := (BitVec 64)

abbrev PMOVSR_Type := (BitVec 32)

abbrev PMOVSSET_EL0_Type := (BitVec 64)

abbrev PMOVSSET_Type := (BitVec 32)

abbrev PMOVS_Type := (BitVec 64)

abbrev PMPCSCTL_Type := (BitVec 64)

abbrev PMPCSR_Type := (BitVec 64)

abbrev PMPIDR0_Type := (BitVec 32)

abbrev PMPIDR1_Type := (BitVec 32)

abbrev PMPIDR2_Type := (BitVec 32)

abbrev PMPIDR3_Type := (BitVec 32)

abbrev PMPIDR4_Type := (BitVec 32)

abbrev PMSCR_EL1_Type := (BitVec 64)

abbrev PMSCR_EL2_Type := (BitVec 64)

abbrev PMSDSFR_EL1_Type := (BitVec 64)

abbrev PMSELR_EL0_Type := (BitVec 64)

abbrev PMSELR_Type := (BitVec 32)

abbrev PMSEVFR_EL1_Type := (BitVec 64)

abbrev PMSFCR_EL1_Type := (BitVec 64)

abbrev PMSICR_EL1_Type := (BitVec 64)

abbrev PMSIDR_EL1_Type := (BitVec 64)

abbrev PMSIRR_EL1_Type := (BitVec 64)

abbrev PMSLATFR_EL1_Type := (BitVec 64)

abbrev PMSNEVFR_EL1_Type := (BitVec 64)

abbrev PMSSCR_EL1_Type := (BitVec 64)

abbrev PMSWINC_EL0_Type := (BitVec 64)

abbrev PMSWINC_Type := (BitVec 32)

abbrev PMUACR_EL1_Type := (BitVec 64)

abbrev PMUSERENR_EL0_Type := (BitVec 64)

abbrev PMUSERENR_Type := (BitVec 32)

abbrev PMVCIDSR_Type := (BitVec 64)

abbrev PMVIDSR_Type := (BitVec 32)

abbrev PMXEVCNTR_EL0_Type := (BitVec 64)

abbrev PMZR_EL0_Type := (BitVec 64)

abbrev POR_EL0_Type := (BitVec 64)

abbrev POR_EL1_Type := (BitVec 64)

abbrev POR_EL2_Type := (BitVec 64)

abbrev POR_EL3_Type := (BitVec 64)

abbrev PRRR_Type := (BitVec 32)

abbrev RCWMASK_EL1_Type := (BitVec 128)

abbrev RCWSMASK_EL1_Type := (BitVec 128)

abbrev RGSR_EL1_Type := (BitVec 64)

abbrev RMR_EL1_Type := (BitVec 64)

abbrev RMR_EL2_Type := (BitVec 64)

abbrev RMR_EL3_Type := (BitVec 64)

abbrev RMR_Type := (BitVec 32)

abbrev RNDRRS_Type := (BitVec 64)

abbrev RNDR_Type := (BitVec 64)

abbrev RVBAR_EL1_Type := (BitVec 64)

abbrev RVBAR_EL2_Type := (BitVec 64)

abbrev RVBAR_EL3_Type := (BitVec 64)

abbrev S1PIRType := (BitVec 64)

abbrev S1PORType := (BitVec 64)

abbrev S2PIRType := (BitVec 64)

abbrev S2PIR_EL2_Type := (BitVec 64)

abbrev S2POR_EL1_Type := (BitVec 64)

abbrev SCRType := (BitVec 64)

abbrev SCR_EL3_Type := (BitVec 64)

abbrev SCR_Type := (BitVec 32)

abbrev SCTLR2_EL1_Type := (BitVec 64)

abbrev SCTLR2_EL2_Type := (BitVec 64)

abbrev SCTLR2_EL3_Type := (BitVec 64)

abbrev SCTLRType := (BitVec 64)

abbrev SCTLR_EL1_Type := (BitVec 64)

abbrev SCTLR_EL2_Type := (BitVec 64)

abbrev SCTLR_EL3_Type := (BitVec 64)

abbrev SCTLR_Type := (BitVec 32)

abbrev SDCR_Type := (BitVec 32)

abbrev SDER32_EL2_Type := (BitVec 64)

abbrev SDER32_EL3_Type := (BitVec 64)

abbrev SDER_Type := (BitVec 32)

abbrev SMCR_EL1_Type := (BitVec 64)

abbrev SMCR_EL2_Type := (BitVec 64)

abbrev SMCR_EL3_Type := (BitVec 64)

abbrev SMIDR_EL1_Type := (BitVec 64)

abbrev SMPRIMAP_EL2_Type := (BitVec 64)

abbrev SMPRI_EL1_Type := (BitVec 64)

abbrev SPMACCESSR_EL1_Type := (BitVec 64)

abbrev SPMACCESSR_EL2_Type := (BitVec 64)

abbrev SPMACCESSR_EL3_Type := (BitVec 64)

abbrev SPMSELR_EL0_Type := (BitVec 64)

abbrev SPSR_EL1_Type := (BitVec 64)

abbrev SPSR_EL2_Type := (BitVec 64)

abbrev SPSR_EL3_Type := (BitVec 64)

abbrev SPSR_abt_Type := (BitVec 64)

abbrev SPSR_fiq_Type := (BitVec 64)

abbrev SPSR_hyp_Type := (BitVec 32)

abbrev SPSR_irq_Type := (BitVec 64)

abbrev SPSR_mon_Type := (BitVec 32)

abbrev SPSR_svc_Type := (BitVec 32)

abbrev SPSR_und_Type := (BitVec 64)

abbrev TCR2_EL1_Type := (BitVec 64)

abbrev TCR2_EL2_Type := (BitVec 64)

abbrev TCR_EL1_Type := (BitVec 64)

abbrev TCR_EL2_Type := (BitVec 64)

abbrev TCR_EL3_Type := (BitVec 64)

abbrev TFSRE0_EL1_Type := (BitVec 64)

abbrev TFSR_EL1_Type := (BitVec 64)

abbrev TFSR_EL2_Type := (BitVec 64)

abbrev TFSR_EL3_Type := (BitVec 64)

abbrev TLBTR_Type := (BitVec 32)

abbrev TRFCR_EL1_Type := (BitVec 64)

abbrev TRFCR_EL2_Type := (BitVec 64)

abbrev TRFCR_Type := (BitVec 32)

abbrev TTBCR2_Type := (BitVec 32)

abbrev TTBCR_Type := (BitVec 32)

abbrev TTBR0_EL1_Type := (BitVec 128)

abbrev TTBR0_EL2_Type := (BitVec 128)

abbrev TTBR0_EL3_Type := (BitVec 64)

abbrev TTBR0_Type := (BitVec 64)

abbrev TTBR1_EL1_Type := (BitVec 128)

abbrev TTBR1_EL2_Type := (BitVec 128)

abbrev TTBR1_Type := (BitVec 64)

abbrev VDFSR_Type := (BitVec 32)

abbrev VDISR_EL2_Type := (BitVec 64)

abbrev VDISR_Type := (BitVec 32)

abbrev VMECID_A_EL2_Type := (BitVec 64)

abbrev VMECID_P_EL2_Type := (BitVec 64)

abbrev VMPIDR_EL2_Type := (BitVec 64)

abbrev VMPIDR_Type := (BitVec 32)

abbrev VNCR_EL2_Type := (BitVec 64)

abbrev VPIDR_EL2_Type := (BitVec 64)

abbrev VPIDR_Type := (BitVec 32)

abbrev VSESR_EL2_Type := (BitVec 64)

abbrev VSTCR_EL2_Type := (BitVec 64)

abbrev VSTTBR_EL2_Type := (BitVec 64)

abbrev VTCR_EL2_Type := (BitVec 64)

abbrev VTCR_Type := (BitVec 32)

abbrev VTTBR_EL2_Type := (BitVec 128)

abbrev VTTBR_Type := (BitVec 64)

abbrev ZCR_EL1_Type := (BitVec 64)

abbrev ZCR_EL2_Type := (BitVec 64)

abbrev ZCR_EL3_Type := (BitVec 64)

inductive Feature where | FEAT_AA32EL0 | FEAT_AA32EL1 | FEAT_AA32EL2 | FEAT_AA32EL3 | FEAT_AA64EL0 | FEAT_AA64EL1 | FEAT_AA64EL2 | FEAT_AA64EL3 | FEAT_EL0 | FEAT_EL1 | FEAT_EL2 | FEAT_EL3 | FEAT_AES | FEAT_AdvSIMD | FEAT_CSV2_1p1 | FEAT_CSV2_1p2 | FEAT_CSV2_2 | FEAT_CSV2_3 | FEAT_DoubleLock | FEAT_ETMv4 | FEAT_ETMv4p1 | FEAT_ETMv4p2 | FEAT_ETMv4p3 | FEAT_ETMv4p4 | FEAT_ETMv4p5 | FEAT_ETMv4p6 | FEAT_ETS2 | FEAT_FP | FEAT_GICv3 | FEAT_GICv3_LEGACY | FEAT_GICv3_TDIR | FEAT_GICv3p1 | FEAT_GICv4 | FEAT_GICv4p1 | FEAT_IVIPT | FEAT_PCSRv8 | FEAT_PMULL | FEAT_PMUv3 | FEAT_PMUv3_EXT | FEAT_PMUv3_EXT32 | FEAT_SHA1 | FEAT_SHA256 | FEAT_TRC_EXT | FEAT_TRC_SR | FEAT_nTLBPA | FEAT_CRC32 | FEAT_Debugv8p1 | FEAT_HAFDBS | FEAT_HPDS | FEAT_LOR | FEAT_LSE | FEAT_PAN | FEAT_PMUv3p1 | FEAT_RDM | FEAT_VHE | FEAT_VMID16 | FEAT_AA32BF16 | FEAT_AA32HPD | FEAT_AA32I8MM | FEAT_ASMv8p2 | FEAT_DPB | FEAT_Debugv8p2 | FEAT_EDHSR | FEAT_F32MM | FEAT_F64MM | FEAT_FP16 | FEAT_HPDS2 | FEAT_I8MM | FEAT_IESB | FEAT_LPA | FEAT_LSMAOC | FEAT_LVA | FEAT_MPAM | FEAT_PAN2 | FEAT_PCSRv8p2 | FEAT_RAS | FEAT_SHA3 | FEAT_SHA512 | FEAT_SM3 | FEAT_SM4 | FEAT_SPE | FEAT_SVE | FEAT_TTCNP | FEAT_UAO | FEAT_VPIPT | FEAT_XNX | FEAT_CCIDX | FEAT_CONSTPACFIELD | FEAT_EPAC | FEAT_FCMA | FEAT_FPAC | FEAT_FPACCOMBINE | FEAT_JSCVT | FEAT_LRCPC | FEAT_NV | FEAT_PACIMP | FEAT_PACQARMA3 | FEAT_PACQARMA5 | FEAT_PAuth | FEAT_SPEv1p1 | FEAT_AMUv1 | FEAT_BBM | FEAT_CNTSC | FEAT_DIT | FEAT_Debugv8p4 | FEAT_DotProd | FEAT_DoubleFault | FEAT_FHM | FEAT_FlagM | FEAT_IDST | FEAT_LRCPC2 | FEAT_LSE2 | FEAT_NV2 | FEAT_PMUv3p4 | FEAT_RASSAv1p1 | FEAT_RASv1p1 | FEAT_S2FWB | FEAT_SEL2 | FEAT_TLBIOS | FEAT_TLBIRANGE | FEAT_TRF | FEAT_TTL | FEAT_TTST | FEAT_BTI | FEAT_CSV2 | FEAT_CSV3 | FEAT_DPB2 | FEAT_E0PD | FEAT_EVT | FEAT_ExS | FEAT_FRINTTS | FEAT_FlagM2 | FEAT_GTG | FEAT_MTE | FEAT_MTE2 | FEAT_PMUv3p5 | FEAT_RNG | FEAT_RNG_TRAP | FEAT_SB | FEAT_SPECRES | FEAT_SSBS | FEAT_SSBS2 | FEAT_AMUv1p1 | FEAT_BF16 | FEAT_DGH | FEAT_ECV | FEAT_FGT | FEAT_HPMN0 | FEAT_MPAMv0p1 | FEAT_MPAMv1p1 | FEAT_MTPMU | FEAT_PAuth2 | FEAT_TWED | FEAT_AFP | FEAT_EBF16 | FEAT_HCX | FEAT_LPA2 | FEAT_LS64 | FEAT_LS64_ACCDATA | FEAT_LS64_V | FEAT_MTE3 | FEAT_PAN3 | FEAT_PMUv3p7 | FEAT_RPRES | FEAT_SPEv1p2 | FEAT_WFxT | FEAT_XS | FEAT_CMOW | FEAT_Debugv8p8 | FEAT_GICv3_NMI | FEAT_HBC | FEAT_MOPS | FEAT_NMI | FEAT_PMUv3_EXT64 | FEAT_PMUv3_TH | FEAT_PMUv3p8 | FEAT_SCTLR2 | FEAT_SPEv1p3 | FEAT_TCR2 | FEAT_TIDCP1 | FEAT_ADERR | FEAT_AIE | FEAT_ANERR | FEAT_CLRBHB | FEAT_CSSC | FEAT_Debugv8p9 | FEAT_DoubleFault2 | FEAT_ECBHB | FEAT_FGT2 | FEAT_HAFT | FEAT_LRCPC3 | FEAT_MTE4 | FEAT_MTE_ASYM_FAULT | FEAT_MTE_ASYNC | FEAT_MTE_CANONICAL_TAGS | FEAT_MTE_NO_ADDRESS_TAGS | FEAT_MTE_PERM | FEAT_MTE_STORE_ONLY | FEAT_MTE_TAGGED_FAR | FEAT_PCSRv8p9 | FEAT_PFAR | FEAT_PMUv3_EDGE | FEAT_PMUv3_ICNTR | FEAT_PMUv3_SS | FEAT_PMUv3p9 | FEAT_PRFMSLC | FEAT_RASSAv2 | FEAT_RASv2 | FEAT_RPRFM | FEAT_S1PIE | FEAT_S1POE | FEAT_S2PIE | FEAT_S2POE | FEAT_SPECRES2 | FEAT_SPE_CRR | FEAT_SPE_FDS | FEAT_SPEv1p4 | FEAT_SPMU | FEAT_THE | FEAT_DoPD | FEAT_ETE | FEAT_SVE2 | FEAT_SVE_AES | FEAT_SVE_BitPerm | FEAT_SVE_PMULL128 | FEAT_SVE_SHA3 | FEAT_SVE_SM4 | FEAT_TME | FEAT_TRBE | FEAT_ETEv1p1 | FEAT_BRBE | FEAT_ETEv1p2 | FEAT_RME | FEAT_SME | FEAT_SME_F64F64 | FEAT_SME_FA64 | FEAT_SME_I16I64 | FEAT_BRBEv1p1 | FEAT_MEC | FEAT_SME2 | FEAT_ABLE | FEAT_CHK | FEAT_D128 | FEAT_EBEP | FEAT_ETEv1p3 | FEAT_GCS | FEAT_ITE | FEAT_LSE128 | FEAT_LVA3 | FEAT_SEBEP | FEAT_SME2p1 | FEAT_SME_F16F16 | FEAT_SVE2p1 | FEAT_SVE_B16B16 | FEAT_SYSINSTR128 | FEAT_SYSREG128 | FEAT_TRBE_EXT | FEAT_TRBE_MPAM
  deriving BEq, Inhabited, Repr
  open Feature

inductive ArchVersion where | v8Ap0 | v8Ap1 | v8Ap2 | v8Ap3 | v8Ap4 | v8Ap5 | v8Ap6 | v8Ap7 | v8Ap8 | v8Ap9 | v9Ap0 | v9Ap1 | v9Ap2 | v9Ap3 | v9Ap4
  deriving BEq, Inhabited, Repr
  open ArchVersion

inductive Signal where | Signal_Low | Signal_High
  deriving BEq, Inhabited, Repr
  open Signal

inductive SecurityState where | SS_NonSecure | SS_Root | SS_Realm | SS_Secure
  deriving BEq, Inhabited, Repr
  open SecurityState

structure ProcState where
  N : (BitVec 1)
  Z : (BitVec 1)
  C : (BitVec 1)
  V : (BitVec 1)
  D : (BitVec 1)
  A : (BitVec 1)
  I : (BitVec 1)
  F : (BitVec 1)
  EXLOCK : (BitVec 1)
  PAN : (BitVec 1)
  UAO : (BitVec 1)
  DIT : (BitVec 1)
  TCO : (BitVec 1)
  PM : (BitVec 1)
  PPEND : (BitVec 1)
  BTYPE : (BitVec 2)
  ZA : (BitVec 1)
  SM : (BitVec 1)
  ALLINT : (BitVec 1)
  SS : (BitVec 1)
  IL : (BitVec 1)
  EL : (BitVec 2)
  nRW : (BitVec 1)
  SP : (BitVec 1)
  Q : (BitVec 1)
  GE : (BitVec 4)
  SSBS : (BitVec 1)
  IT : (BitVec 8)
  J : (BitVec 1)
  T : (BitVec 1)
  E : (BitVec 1)
  M : (BitVec 5)
  deriving BEq, Inhabited, Repr

inductive PrivilegeLevel where | PL3 | PL2 | PL1 | PL0
  deriving BEq, Inhabited, Repr
  open PrivilegeLevel

inductive InstrSet where | InstrSet_A64 | InstrSet_A32 | InstrSet_T32
  deriving BEq, Inhabited, Repr
  open InstrSet

inductive DSBAlias where | DSBAlias_SSBB | DSBAlias_PSSBB | DSBAlias_DSB
  deriving BEq, Inhabited, Repr
  open DSBAlias

inductive WFxType where | WFxType_WFE | WFxType_WFI | WFxType_WFET | WFxType_WFIT
  deriving BEq, Inhabited, Repr
  open WFxType

inductive ExceptionalOccurrenceTargetState where | AArch32_NonDebugState | AArch64_NonDebugState | DebugState
  deriving BEq, Inhabited, Repr
  open ExceptionalOccurrenceTargetState

abbrev PARTIDtype := (BitVec 16)

abbrev PMGtype := (BitVec 8)

inductive PARTIDspaceType where | PIdSpace_Secure | PIdSpace_Root | PIdSpace_Realm | PIdSpace_NonSecure
  deriving BEq, Inhabited, Repr
  open PARTIDspaceType

structure MPAMinfo where
  mpam_sp : PARTIDspaceType
  partid : PARTIDtype
  pmg : PMGtype
  deriving BEq, Inhabited, Repr

inductive AccessType where | AccessType_IFETCH | AccessType_GPR | AccessType_ASIMD | AccessType_SVE | AccessType_SME | AccessType_IC | AccessType_DC | AccessType_DCZero | AccessType_AT | AccessType_NV2 | AccessType_SPE | AccessType_GCS | AccessType_GPTW | AccessType_TTW
  deriving BEq, Inhabited, Repr
  open AccessType

inductive MemOp where | MemOp_LOAD | MemOp_STORE | MemOp_PREFETCH
  deriving BEq, Inhabited, Repr
  open MemOp

inductive VARange where | VARange_LOWER | VARange_UPPER
  deriving BEq, Inhabited, Repr
  open VARange

inductive MemAtomicOp where | MemAtomicOp_GCSSS1 | MemAtomicOp_ADD | MemAtomicOp_BIC | MemAtomicOp_EOR | MemAtomicOp_ORR | MemAtomicOp_SMAX | MemAtomicOp_SMIN | MemAtomicOp_UMAX | MemAtomicOp_UMIN | MemAtomicOp_SWP | MemAtomicOp_CAS
  deriving BEq, Inhabited, Repr
  open MemAtomicOp

inductive CacheOp where | CacheOp_Clean | CacheOp_Invalidate | CacheOp_CleanInvalidate
  deriving BEq, Inhabited, Repr
  open CacheOp

inductive CacheOpScope where | CacheOpScope_SetWay | CacheOpScope_PoU | CacheOpScope_PoC | CacheOpScope_PoE | CacheOpScope_PoP | CacheOpScope_PoDP | CacheOpScope_PoPA | CacheOpScope_ALLU | CacheOpScope_ALLUIS
  deriving BEq, Inhabited, Repr
  open CacheOpScope

inductive CacheType where | CacheType_Data | CacheType_Tag | CacheType_Data_Tag | CacheType_Instruction
  deriving BEq, Inhabited, Repr
  open CacheType

inductive CachePASpace where | CPAS_NonSecure | CPAS_Any | CPAS_RealmNonSecure | CPAS_Realm | CPAS_Root | CPAS_SecureNonSecure | CPAS_Secure
  deriving BEq, Inhabited, Repr
  open CachePASpace

structure AccessDescriptor where
  acctype : AccessType
  el : (BitVec 2)
  ss : SecurityState
  acqsc : Bool
  acqpc : Bool
  relsc : Bool
  limitedordered : Bool
  exclusive : Bool
  atomicop : Bool
  modop : MemAtomicOp
  nontemporal : Bool
  read : Bool
  write : Bool
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  pan : Bool
  transactional : Bool
  nonfault : Bool
  firstfault : Bool
  first : Bool
  contiguous : Bool
  streamingsve : Bool
  ls64 : Bool
  mops : Bool
  rcw : Bool
  rcws : Bool
  toplevel : Bool
  varange : VARange
  a32lsmd : Bool
  tagchecked : Bool
  tagaccess : Bool
  mpam : MPAMinfo
  deriving BEq, Inhabited, Repr

inductive MemType where | MemType_Normal | MemType_Device
  deriving BEq, Inhabited, Repr
  open MemType

inductive DeviceType where | DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE
  deriving BEq, Inhabited, Repr
  open DeviceType

structure MemAttrHints where
  attrs : (BitVec 2)
  hints : (BitVec 2)
  transient : Bool
  deriving BEq, Inhabited, Repr

inductive Shareability where | Shareability_NSH | Shareability_ISH | Shareability_OSH
  deriving BEq, Inhabited, Repr
  open Shareability

inductive MemTagType where | MemTag_Untagged | MemTag_AllocationTagged | MemTag_CanonicallyTagged
  deriving BEq, Inhabited, Repr
  open MemTagType

structure MemoryAttributes where
  memtype : MemType
  device : DeviceType
  inner : MemAttrHints
  outer : MemAttrHints
  shareability : Shareability
  tags : MemTagType
  notagaccess : Bool
  xs : (BitVec 1)
  deriving BEq, Inhabited, Repr

inductive PASpace where | PAS_NonSecure | PAS_Secure | PAS_Root | PAS_Realm
  deriving BEq, Inhabited, Repr
  open PASpace

structure FullAddress where
  paspace : PASpace
  address : (BitVec 56)
  deriving BEq, Inhabited, Repr

inductive GPCF where | GPCF_None | GPCF_AddressSize | GPCF_Walk | GPCF_EABT | GPCF_Fail
  deriving BEq, Inhabited, Repr
  open GPCF

structure GPCFRecord where
  gpf : GPCF
  level : Int
  deriving BEq, Inhabited, Repr

inductive Fault where | Fault_None | Fault_AccessFlag | Fault_Alignment | Fault_Background | Fault_Domain | Fault_Permission | Fault_Translation | Fault_AddressSize | Fault_SyncExternal | Fault_SyncExternalOnWalk | Fault_SyncParity | Fault_SyncParityOnWalk | Fault_GPCFOnWalk | Fault_GPCFOnOutput | Fault_AsyncParity | Fault_AsyncExternal | Fault_TagCheck | Fault_Debug | Fault_TLBConflict | Fault_BranchTarget | Fault_HWUpdateAccessFlag | Fault_Lockdown | Fault_Exclusive | Fault_ICacheMaint
  deriving BEq, Inhabited, Repr
  open Fault

inductive ErrorState where | ErrorState_UC | ErrorState_UEU | ErrorState_UEO | ErrorState_UER | ErrorState_CE | ErrorState_Uncategorized | ErrorState_IMPDEF
  deriving BEq, Inhabited, Repr
  open ErrorState

structure FaultRecord where
  statuscode : Fault
  access : AccessDescriptor
  ipaddress : FullAddress
  gpcf : GPCFRecord
  paddress : FullAddress
  gpcfs2walk : Bool
  s2fs1walk : Bool
  write : Bool
  s1tagnotdata : Bool
  tagaccess : Bool
  level : Int
  extflag : (BitVec 1)
  secondstage : Bool
  assuredonly : Bool
  toplevel : Bool
  overlay : Bool
  dirtybit : Bool
  domain : (BitVec 4)
  merrorstate : ErrorState
  debugmoe : (BitVec 4)
  deriving BEq, Inhabited, Repr

structure PhysMemRetStatus where
  statuscode : Fault
  extflag : (BitVec 1)
  merrorstate : ErrorState
  store64bstatus : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure Permissions where
  ap_table : (BitVec 2)
  xn_table : (BitVec 1)
  pxn_table : (BitVec 1)
  uxn_table : (BitVec 1)
  ap : (BitVec 3)
  xn : (BitVec 1)
  uxn : (BitVec 1)
  pxn : (BitVec 1)
  ppi : (BitVec 4)
  upi : (BitVec 4)
  ndirty : (BitVec 1)
  s2pi : (BitVec 4)
  s2dirty : (BitVec 1)
  po_index : (BitVec 4)
  s2po_index : (BitVec 4)
  s2ap : (BitVec 2)
  s2tag_na : (BitVec 1)
  s2xnx : (BitVec 1)
  s2xn : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure S1AccessControls where
  r : (BitVec 1)
  w : (BitVec 1)
  x : (BitVec 1)
  gcs : (BitVec 1)
  overlay : Bool
  or : (BitVec 1)
  ow : (BitVec 1)
  ox : (BitVec 1)
  wxn : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure S2AccessControls where
  r : (BitVec 1)
  w : (BitVec 1)
  x : (BitVec 1)
  r_rcw : (BitVec 1)
  w_rcw : (BitVec 1)
  r_mmu : (BitVec 1)
  w_mmu : (BitVec 1)
  toplevel0 : (BitVec 1)
  toplevel1 : (BitVec 1)
  overlay : Bool
  or : (BitVec 1)
  ow : (BitVec 1)
  ox : (BitVec 1)
  or_rcw : (BitVec 1)
  ow_rcw : (BitVec 1)
  or_mmu : (BitVec 1)
  ow_mmu : (BitVec 1)
  deriving BEq, Inhabited, Repr

inductive MBReqDomain where | MBReqDomain_Nonshareable | MBReqDomain_InnerShareable | MBReqDomain_OuterShareable | MBReqDomain_FullSystem
  deriving BEq, Inhabited, Repr
  open MBReqDomain

inductive MBReqTypes where | MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All
  deriving BEq, Inhabited, Repr
  open MBReqTypes

inductive PrefetchHint where | Prefetch_READ | Prefetch_WRITE | Prefetch_EXEC
  deriving BEq, Inhabited, Repr
  open PrefetchHint

inductive Unpredictable where | Unpredictable_VMSR | Unpredictable_WBOVERLAPLD | Unpredictable_WBOVERLAPST | Unpredictable_LDPOVERLAP | Unpredictable_BASEOVERLAP | Unpredictable_DATAOVERLAP | Unpredictable_DEVPAGE2 | Unpredictable_INSTRDEVICE | Unpredictable_RESCPACR | Unpredictable_RESMAIR | Unpredictable_S1CTAGGED | Unpredictable_S2RESMEMATTR | Unpredictable_RESTEXCB | Unpredictable_RESPRRR | Unpredictable_RESDACR | Unpredictable_RESVTCRS | Unpredictable_RESTnSZ | Unpredictable_RESTCF | Unpredictable_DEVICETAGSTORE | Unpredictable_OORTnSZ | Unpredictable_LARGEIPA | Unpredictable_ESRCONDPASS | Unpredictable_ILZEROIT | Unpredictable_ILZEROT | Unpredictable_BPVECTORCATCHPRI | Unpredictable_VCMATCHHALF | Unpredictable_VCMATCHDAPA | Unpredictable_WPMASKANDBAS | Unpredictable_WPBASCONTIGUOUS | Unpredictable_RESWPMASK | Unpredictable_WPMASKEDBITS | Unpredictable_RESBPWPCTRL | Unpredictable_BPNOTIMPL | Unpredictable_RESBPTYPE | Unpredictable_RESMDSELR | Unpredictable_BPNOTCTXCMP | Unpredictable_BPMATCHHALF | Unpredictable_BPMISMATCHHALF | Unpredictable_BPLINKINGDISABLED | Unpredictable_RESBPMASK | Unpredictable_BPMASK | Unpredictable_BPMASKEDBITS | Unpredictable_BPLINKEDADDRMATCH | Unpredictable_RESTARTALIGNPC | Unpredictable_RESTARTZEROUPPERPC | Unpredictable_ZEROUPPER | Unpredictable_ERETZEROUPPERPC | Unpredictable_A32FORCEALIGNPC | Unpredictable_SMD | Unpredictable_NONFAULT | Unpredictable_SVEZEROUPPER | Unpredictable_SVELDNFDATA | Unpredictable_SVELDNFZERO | Unpredictable_CHECKSPNONEACTIVE | Unpredictable_SMEZEROUPPER | Unpredictable_NVNV1 | Unpredictable_Shareability | Unpredictable_AFUPDATE | Unpredictable_DBUPDATE | Unpredictable_IESBinDebug | Unpredictable_BADPMSFCR | Unpredictable_ZEROBTYPE | Unpredictable_EL2TIMESTAMP | Unpredictable_EL1TIMESTAMP | Unpredictable_RESERVEDNSxB | Unpredictable_WFxTDEBUG | Unpredictable_LS64UNSUPPORTED | Unpredictable_MISALIGNEDATOMIC | Unpredictable_CLEARERRITEZERO | Unpredictable_ALUEXCEPTIONRETURN | Unpredictable_IGNORETRAPINDEBUG | Unpredictable_DBGxVR_RESS | Unpredictable_PMUEVENTCOUNTER | Unpredictable_PMSCR_PCT | Unpredictable_CounterReservedForEL2 | Unpredictable_BRBFILTRATE | Unpredictable_MOPSOVERLAP31 | Unpredictable_STOREONLYTAGCHECKEDCAS | Unpredictable_RESTC
  deriving BEq, Inhabited, Repr
  open Unpredictable

inductive Constraint where | Constraint_NONE | Constraint_UNKNOWN | Constraint_UNDEF | Constraint_UNDEFEL0 | Constraint_NOP | Constraint_TRUE | Constraint_FALSE | Constraint_DISABLED | Constraint_UNCOND | Constraint_COND | Constraint_ADDITIONAL_DECODE | Constraint_WBSUPPRESS | Constraint_FAULT | Constraint_LIMITED_ATOMICITY | Constraint_NVNV1_00 | Constraint_NVNV1_01 | Constraint_NVNV1_11 | Constraint_EL1TIMESTAMP | Constraint_EL2TIMESTAMP | Constraint_OSH | Constraint_ISH | Constraint_NSH | Constraint_NC | Constraint_WT | Constraint_WB | Constraint_FORCE | Constraint_FORCENOSLCHECK | Constraint_MAPTOALLOCATED | Constraint_PMSCR_PCT_VIRT
  deriving BEq, Inhabited, Repr
  open Constraint

structure CacheRecord where
  acctype : AccessType
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  regval : (BitVec 64)
  paddress : FullAddress
  vaddress : (BitVec 64)
  setnum : Int
  waynum : Int
  level : Int
  shareability : Shareability
  translated : Bool
  is_vmid_valid : Bool
  vmid : (BitVec 16)
  is_asid_valid : Bool
  asid : (BitVec 16)
  security : SecurityState
  cpas : CachePASpace
  deriving BEq, Inhabited, Repr

inductive RestrictType where | RestrictType_DataValue | RestrictType_ControlFlow | RestrictType_CachePrefetch | RestrictType_Other
  deriving BEq, Inhabited, Repr
  open RestrictType

structure ExecutionCntxt where
  is_vmid_valid : Bool
  all_vmid : Bool
  vmid : (BitVec 16)
  is_asid_valid : Bool
  all_asid : Bool
  asid : (BitVec 16)
  target_el : (BitVec 2)
  security : SecurityState
  restriction : RestrictType
  deriving BEq, Inhabited, Repr

inductive FPExc where | FPExc_InvalidOp | FPExc_DivideByZero | FPExc_Overflow | FPExc_Underflow | FPExc_Inexact | FPExc_InputDenorm
  deriving BEq, Inhabited, Repr
  open FPExc

inductive FPRounding where | FPRounding_TIEEVEN | FPRounding_POSINF | FPRounding_NEGINF | FPRounding_ZERO | FPRounding_TIEAWAY | FPRounding_ODD
  deriving BEq, Inhabited, Repr
  open FPRounding

inductive FPType where | FPType_Zero | FPType_Denormal | FPType_Nonzero | FPType_Infinity | FPType_QNaN | FPType_SNaN
  deriving BEq, Inhabited, Repr
  open FPType

inductive BranchType where | BranchType_DIRCALL | BranchType_INDCALL | BranchType_ERET | BranchType_DBGEXIT | BranchType_RET | BranchType_DIR | BranchType_INDIR | BranchType_EXCEPTION | BranchType_TMFAIL | BranchType_RESET | BranchType_UNKNOWN
  deriving BEq, Inhabited, Repr
  open BranchType

inductive InterruptID where | InterruptID_PMUIRQ | InterruptID_COMMIRQ | InterruptID_CTIIRQ | InterruptID_COMMRX | InterruptID_COMMTX | InterruptID_CNTP | InterruptID_CNTHP | InterruptID_CNTHPS | InterruptID_CNTPS | InterruptID_CNTV | InterruptID_CNTHV | InterruptID_CNTHVS | InterruptID_PMBIRQ
  deriving BEq, Inhabited, Repr
  open InterruptID

inductive Exception where | Exception_Uncategorized | Exception_WFxTrap | Exception_CP15RTTrap | Exception_CP15RRTTrap | Exception_CP14RTTrap | Exception_CP14DTTrap | Exception_CP14RRTTrap | Exception_AdvSIMDFPAccessTrap | Exception_FPIDTrap | Exception_LDST64BTrap | Exception_PACTrap | Exception_IllegalState | Exception_SupervisorCall | Exception_HypervisorCall | Exception_MonitorCall | Exception_SystemRegisterTrap | Exception_ERetTrap | Exception_InstructionAbort | Exception_PCAlignment | Exception_DataAbort | Exception_NV2DataAbort | Exception_PACFail | Exception_SPAlignment | Exception_FPTrappedException | Exception_SError | Exception_Breakpoint | Exception_SoftwareStep | Exception_Watchpoint | Exception_NV2Watchpoint | Exception_SoftwareBreakpoint | Exception_VectorCatch | Exception_IRQ | Exception_SVEAccessTrap | Exception_SMEAccessTrap | Exception_TSTARTAccessTrap | Exception_GPC | Exception_BranchTarget | Exception_MemCpyMemSet | Exception_GCSFail | Exception_SystemRegister128Trap | Exception_FIQ
  deriving BEq, Inhabited, Repr
  open Exception

structure ExceptionRecord where
  exceptype : Exception
  syndrome : (BitVec 25)
  syndrome2 : (BitVec 24)
  paddress : FullAddress
  vaddress : (BitVec 64)
  ipavalid : Bool
  pavalid : Bool
  NS : (BitVec 1)
  ipaddress : (BitVec 56)
  trappedsyscallinst : Bool
  deriving BEq, Inhabited, Repr

inductive TranslationStage where | TranslationStage_1 | TranslationStage_12
  deriving BEq, Inhabited, Repr
  open TranslationStage

inductive ATAccess where | ATAccess_Read | ATAccess_Write | ATAccess_ReadPAN | ATAccess_WritePAN
  deriving BEq, Inhabited, Repr
  open ATAccess

inductive Regime where | Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10
  deriving BEq, Inhabited, Repr
  open Regime

inductive TGx where | TGx_4KB | TGx_16KB | TGx_64KB
  deriving BEq, Inhabited, Repr
  open TGx

inductive DescriptorType where | DescriptorType_Table | DescriptorType_Leaf | DescriptorType_Invalid
  deriving BEq, Inhabited, Repr
  open DescriptorType

inductive SDFType where | SDFType_Table | SDFType_Invalid | SDFType_Supersection | SDFType_Section | SDFType_LargePage | SDFType_SmallPage
  deriving BEq, Inhabited, Repr
  open SDFType

structure TTWState where
  istable : Bool
  level : Int
  baseaddress : FullAddress
  contiguous : (BitVec 1)
  s1assured : Bool
  s2assuredonly : (BitVec 1)
  disch : (BitVec 1)
  nG : (BitVec 1)
  guardedpage : (BitVec 1)
  sdftype : SDFType
  domain : (BitVec 4)
  memattrs : MemoryAttributes
  permissions : Permissions
  deriving BEq, Inhabited, Repr

structure S1TTWParams where
  ha : (BitVec 1)
  hd : (BitVec 1)
  tbi : (BitVec 1)
  tbid : (BitVec 1)
  nfd : (BitVec 1)
  e0pd : (BitVec 1)
  d128 : (BitVec 1)
  aie : (BitVec 1)
  mair2 : MAIRType
  ds : (BitVec 1)
  ps : (BitVec 3)
  txsz : (BitVec 6)
  epan : (BitVec 1)
  dct : (BitVec 1)
  nv1 : (BitVec 1)
  cmow : (BitVec 1)
  pnch : (BitVec 1)
  disch : (BitVec 1)
  haft : (BitVec 1)
  mtx : (BitVec 1)
  skl : (BitVec 2)
  pie : (BitVec 1)
  pir : S1PIRType
  pire0 : S1PIRType
  emec : (BitVec 1)
  amec : (BitVec 1)
  t0sz : (BitVec 3)
  t1sz : (BitVec 3)
  uwxn : (BitVec 1)
  tgx : TGx
  irgn : (BitVec 2)
  orgn : (BitVec 2)
  sh : (BitVec 2)
  hpd : (BitVec 1)
  ee : (BitVec 1)
  wxn : (BitVec 1)
  ntlsmd : (BitVec 1)
  dc : (BitVec 1)
  sif : (BitVec 1)
  mair : MAIRType
  deriving BEq, Inhabited, Repr

structure S2TTWParams where
  ha : (BitVec 1)
  hd : (BitVec 1)
  sl2 : (BitVec 1)
  ds : (BitVec 1)
  d128 : (BitVec 1)
  sw : (BitVec 1)
  nsw : (BitVec 1)
  sa : (BitVec 1)
  nsa : (BitVec 1)
  ps : (BitVec 3)
  txsz : (BitVec 6)
  fwb : (BitVec 1)
  cmow : (BitVec 1)
  skl : (BitVec 2)
  s2pie : (BitVec 1)
  s2pir : S2PIRType
  tl0 : (BitVec 1)
  tl1 : (BitVec 1)
  assuredonly : (BitVec 1)
  haft : (BitVec 1)
  emec : (BitVec 1)
  s : (BitVec 1)
  t0sz : (BitVec 4)
  tgx : TGx
  sl0 : (BitVec 2)
  irgn : (BitVec 2)
  orgn : (BitVec 2)
  sh : (BitVec 2)
  ee : (BitVec 1)
  ptw : (BitVec 1)
  vm : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure TLBContext where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  nG : (BitVec 1)
  ipaspace : PASpace
  includes_s1_name : Bool
  includes_s2_name : Bool
  includes_gpt_name : Bool
  ia : (BitVec 64)
  tg : TGx
  cnp : (BitVec 1)
  level : Int
  isd128 : Bool
  xs : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure TLBRecord where
  context : TLBContext
  walkstate : TTWState
  blocksize : Int
  contigsize : Int
  s1descriptor : (BitVec 128)
  s2descriptor : (BitVec 128)
  deriving BEq, Inhabited, Repr

structure AddressDescriptor where
  fault : FaultRecord
  memattrs : MemoryAttributes
  paddress : FullAddress
  tlbcontext : TLBContext
  s1assured : Bool
  s2fs1mro : Bool
  mecid : (BitVec 16)
  vaddress : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure TranslationInfo where
  regime : Regime
  vmid : (Option (BitVec 16))
  asid : (Option (BitVec 16))
  va : (BitVec 64)
  s1level : (Option Int)
  s2info : (Option ((BitVec 64) × Int))
  s1params : (Option S1TTWParams)
  s2params : (Option S2TTWParams)
  memattrs : MemoryAttributes
  deriving BEq, Inhabited, Repr

structure TranslationStartInfo where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  va : (BitVec 64)
  cnp : (BitVec 1)
  accdesc : AccessDescriptor
  size : Int
  deriving BEq, Inhabited, Repr

inductive SVECmp where | Cmp_EQ | Cmp_NE | Cmp_GE | Cmp_GT | Cmp_LT | Cmp_LE | Cmp_UN
  deriving BEq, Inhabited, Repr
  open SVECmp

abbrev MAX_VL  : Int := 2048

abbrev MAX_PL  : Int := 256

inductive SMEExceptionType where | SMEExceptionType_AccessTrap | SMEExceptionType_Streaming | SMEExceptionType_NotStreaming | SMEExceptionType_InactiveZA | SMEExceptionType_InaccessibleZT0
  deriving BEq, Inhabited, Repr
  open SMEExceptionType

inductive GCSInstruction where | GCSInstType_PRET | GCSInstType_POPM | GCSInstType_PRETAA | GCSInstType_PRETAB | GCSInstType_SS1 | GCSInstType_SS2 | GCSInstType_POPCX | GCSInstType_POPX
  deriving BEq, Inhabited, Repr
  open GCSInstruction

inductive MOPSStage where | MOPSStage_Prologue | MOPSStage_Main | MOPSStage_Epilogue
  deriving BEq, Inhabited, Repr
  open MOPSStage

structure TMState where
  depth : Int
  Rt : Int
  nPC : (BitVec 64)
  X : (Vector (BitVec 64) 31)
  Z : (Vector (BitVec 2048) 32)
  P : (Vector (BitVec 256) 16)
  FFR : (BitVec 256)
  SP : (BitVec 64)
  FPCR : (BitVec 64)
  FPSR : (BitVec 64)
  ICC_PMR_EL1 : (BitVec 64)
  GCSPR_ELx : (BitVec 64)
  nzcv : (BitVec 4)
  D : (BitVec 1)
  A : (BitVec 1)
  I : (BitVec 1)
  F : (BitVec 1)
  deriving BEq, Inhabited, Repr

inductive TMFailure where | TMFailure_CNCL | TMFailure_DBG | TMFailure_ERR | TMFailure_NEST | TMFailure_SIZE | TMFailure_MEM | TMFailure_TRIVIAL | TMFailure_IMP
  deriving BEq, Inhabited, Repr
  open TMFailure

inductive PGSe where | PGS_4KB | PGS_16KB | PGS_64KB
  deriving BEq, Inhabited, Repr
  open PGSe

structure GPTTable where
  address : (BitVec 56)
  deriving BEq, Inhabited, Repr

structure GPTEntry where
  gpi : (BitVec 4)
  size : Int
  contig_size : Int
  level : Int
  pa : (BitVec 56)
  deriving BEq, Inhabited, Repr

inductive TimeStamp where | TimeStamp_None | TimeStamp_CoreSight | TimeStamp_Physical | TimeStamp_OffsetPhysical | TimeStamp_Virtual
  deriving BEq, Inhabited, Repr
  open TimeStamp

inductive OpType where | OpType_Load | OpType_Store | OpType_LoadAtomic | OpType_Branch | OpType_Other
  deriving BEq, Inhabited, Repr
  open OpType

inductive CountOp where | CountOp_CLZ | CountOp_CLS | CountOp_CNT
  deriving BEq, Inhabited, Repr
  open CountOp

inductive ExtendType where | ExtendType_SXTB | ExtendType_SXTH | ExtendType_SXTW | ExtendType_SXTX | ExtendType_UXTB | ExtendType_UXTH | ExtendType_UXTW | ExtendType_UXTX
  deriving BEq, Inhabited, Repr
  open ExtendType

inductive FPMaxMinOp where | FPMaxMinOp_MAX | FPMaxMinOp_MIN | FPMaxMinOp_MAXNUM | FPMaxMinOp_MINNUM
  deriving BEq, Inhabited, Repr
  open FPMaxMinOp

inductive FPUnaryOp where | FPUnaryOp_ABS | FPUnaryOp_MOV | FPUnaryOp_NEG | FPUnaryOp_SQRT
  deriving BEq, Inhabited, Repr
  open FPUnaryOp

inductive FPConvOp where | FPConvOp_CVT_FtoI | FPConvOp_CVT_ItoF | FPConvOp_MOV_FtoI | FPConvOp_MOV_ItoF | FPConvOp_CVT_FtoI_JS
  deriving BEq, Inhabited, Repr
  open FPConvOp

inductive MoveWideOp where | MoveWideOp_N | MoveWideOp_Z | MoveWideOp_K
  deriving BEq, Inhabited, Repr
  open MoveWideOp

inductive ShiftType where | ShiftType_LSL | ShiftType_LSR | ShiftType_ASR | ShiftType_ROR
  deriving BEq, Inhabited, Repr
  open ShiftType

inductive LogicalOp where | LogicalOp_AND | LogicalOp_EOR | LogicalOp_ORR
  deriving BEq, Inhabited, Repr
  open LogicalOp

inductive SystemHintOp where | SystemHintOp_NOP | SystemHintOp_YIELD | SystemHintOp_WFE | SystemHintOp_WFI | SystemHintOp_SEV | SystemHintOp_SEVL | SystemHintOp_DGH | SystemHintOp_ESB | SystemHintOp_PSB | SystemHintOp_TSB | SystemHintOp_BTI | SystemHintOp_WFET | SystemHintOp_WFIT | SystemHintOp_CLRBHB | SystemHintOp_GCSB | SystemHintOp_CHKFEAT | SystemHintOp_CSDB
  deriving BEq, Inhabited, Repr
  open SystemHintOp

inductive PSTATEField where | PSTATEField_DAIFSet | PSTATEField_DAIFClr | PSTATEField_PAN | PSTATEField_UAO | PSTATEField_DIT | PSTATEField_SSBS | PSTATEField_TCO | PSTATEField_SVCRSM | PSTATEField_SVCRZA | PSTATEField_SVCRSMZA | PSTATEField_ALLINT | PSTATEField_PM | PSTATEField_SP
  deriving BEq, Inhabited, Repr
  open PSTATEField

inductive TLBILevel where | TLBILevel_Any | TLBILevel_Last
  deriving BEq, Inhabited, Repr
  open TLBILevel

inductive TLBIOp where | TLBIOp_DALL | TLBIOp_DASID | TLBIOp_DVA | TLBIOp_IALL | TLBIOp_IASID | TLBIOp_IVA | TLBIOp_ALL | TLBIOp_ASID | TLBIOp_IPAS2 | TLBIPOp_IPAS2 | TLBIOp_VAA | TLBIOp_VA | TLBIPOp_VAA | TLBIPOp_VA | TLBIOp_VMALL | TLBIOp_VMALLS12 | TLBIOp_RIPAS2 | TLBIPOp_RIPAS2 | TLBIOp_RVAA | TLBIOp_RVA | TLBIPOp_RVAA | TLBIPOp_RVA | TLBIOp_RPA | TLBIOp_PAALL
  deriving BEq, Inhabited, Repr
  open TLBIOp

inductive TLBIMemAttr where | TLBI_AllAttr | TLBI_ExcludeXS
  deriving BEq, Inhabited, Repr
  open TLBIMemAttr

structure TLBIRecord where
  op : TLBIOp
  from_aarch64 : Bool
  security : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  level : TLBILevel
  attr : TLBIMemAttr
  ipaspace : PASpace
  address : (BitVec 64)
  end_address_name : (BitVec 64)
  d64 : Bool
  d128 : Bool
  ttl : (BitVec 4)
  tg : (BitVec 2)
  deriving BEq, Inhabited, Repr

inductive VBitOp where | VBitOp_VBIF | VBitOp_VBIT | VBitOp_VBSL | VBitOp_VEOR
  deriving BEq, Inhabited, Repr
  open VBitOp

inductive CompareOp where | CompareOp_GT | CompareOp_GE | CompareOp_EQ | CompareOp_LE | CompareOp_LT
  deriving BEq, Inhabited, Repr
  open CompareOp

inductive ImmediateOp where | ImmediateOp_MOVI | ImmediateOp_MVNI | ImmediateOp_ORR | ImmediateOp_BIC
  deriving BEq, Inhabited, Repr
  open ImmediateOp

inductive ReduceOp where | ReduceOp_FMINNUM | ReduceOp_FMAXNUM | ReduceOp_FMIN | ReduceOp_FMAX | ReduceOp_FADD | ReduceOp_ADD
  deriving BEq, Inhabited, Repr
  open ReduceOp

inductive CrossTriggerIn where | CrossTriggerIn_CrossHalt | CrossTriggerIn_PMUOverflow | CrossTriggerIn_RSVD2 | CrossTriggerIn_RSVD3 | CrossTriggerIn_TraceExtOut0 | CrossTriggerIn_TraceExtOut1 | CrossTriggerIn_TraceExtOut2 | CrossTriggerIn_TraceExtOut3
  deriving BEq, Inhabited, Repr
  open CrossTriggerIn

structure TLBLine where
  tlbrecord : TLBRecord
  valid_name : Bool
  deriving BEq, Inhabited, Repr

structure GPTTLBLine where
  gpt_entry : GPTEntry
  valid_name : Bool
  deriving BEq, Inhabited, Repr

structure InterruptReq where
  take_SE : Bool
  take_vSE : Bool
  take_IRQ : Bool
  take_vIRQ : Bool
  take_FIQ : Bool
  take_vFIQ : Bool
  iesb_req : Bool
  deriving BEq, Inhabited, Repr

inductive __InstrEnc where | __A64 | __A32 | __T16 | __T32
  deriving BEq, Inhabited, Repr
  open __InstrEnc

inductive SRType where | SRType_LSL | SRType_LSR | SRType_ASR | SRType_ROR | SRType_RRX
  deriving BEq, Inhabited, Repr
  open SRType

inductive VCGEType where | VCGEType_signed | VCGEType_unsigned | VCGEType_fp
  deriving BEq, Inhabited, Repr
  open VCGEType

inductive VFPNegMul where | VFPNegMul_VNMLA | VFPNegMul_VNMLS | VFPNegMul_VNMUL
  deriving BEq, Inhabited, Repr
  open VFPNegMul

inductive VCGTtype where | VCGTtype_signed | VCGTtype_unsigned | VCGTtype_fp
  deriving BEq, Inhabited, Repr
  open VCGTtype

inductive VBitOps where | VBitOps_VBIF | VBitOps_VBIT | VBitOps_VBSL
  deriving BEq, Inhabited, Repr
  open VBitOps

abbrev CNTPOFF_EL2_Type := (BitVec 64)

abbrev CNTVOFF_EL2_Type := (BitVec 64)

abbrev DLR_EL0_Type := (BitVec 64)

abbrev DLR_Type := (BitVec 32)

abbrev SP_EL0_Type := (BitVec 64)

abbrev SP_EL1_Type := (BitVec 64)

abbrev SP_EL2_Type := (BitVec 64)

abbrev SP_EL3_Type := (BitVec 64)

abbrev FAR_EL1_Type := (BitVec 64)

abbrev FAR_EL2_Type := (BitVec 64)

abbrev FAR_EL3_Type := (BitVec 64)

abbrev ELR_EL1_Type := (BitVec 64)

abbrev ELR_EL2_Type := (BitVec 64)

abbrev ELR_EL3_Type := (BitVec 64)

abbrev VBAR_EL1_Type := (BitVec 64)

abbrev VBAR_EL2_Type := (BitVec 64)

abbrev VBAR_EL3_Type := (BitVec 64)

abbrev VBAR_Type := (BitVec 32)

abbrev HDFAR_Type := (BitVec 32)

abbrev HIFAR_Type := (BitVec 32)

abbrev ELR_hyp_Type := (BitVec 32)

abbrev HVBAR_Type := (BitVec 32)

abbrev DFAR_Type := (BitVec 32)

abbrev IFAR_Type := (BitVec 32)

inductive arm_acc_type where
  | SAcc_ASIMD (_ : Bool)
  | SAcc_SVE (_ : Bool)
  | SAcc_SME (_ : Bool)
  | SAcc_IC (_ : Unit)
  | SAcc_DC (_ : Unit)
  | SAcc_DCZero (_ : Unit)
  | SAcc_AT (_ : Unit)
  | SAcc_NV2 (_ : Unit)
  | SAcc_SPE (_ : Unit)
  | SAcc_GCS (_ : Unit)
  | SAcc_GPTW (_ : Unit)
  deriving Inhabited, BEq, Repr
  open arm_acc_type

abbrev APIAKeyHi_EL1_Type := (BitVec 64)

abbrev APIAKeyLo_EL1_Type := (BitVec 64)

abbrev APIBKeyHi_EL1_Type := (BitVec 64)

abbrev APIBKeyLo_EL1_Type := (BitVec 64)

abbrev APDAKeyHi_EL1_Type := (BitVec 64)

abbrev APDAKeyLo_EL1_Type := (BitVec 64)

abbrev APDBKeyHi_EL1_Type := (BitVec 64)

abbrev APDBKeyLo_EL1_Type := (BitVec 64)

abbrev APGAKeyHi_EL1_Type := (BitVec 64)

abbrev APGAKeyLo_EL1_Type := (BitVec 64)

abbrev EDWAR_Type := (BitVec 64)

abbrev CTIDEVID1_Type := (BitVec 32)

abbrev CTIDEVID2_Type := (BitVec 32)

abbrev DBGDEVID2_Type := (BitVec 32)

abbrev DBGDSAR_Type := (BitVec 64)

abbrev DBGWFAR_Type := (BitVec 32)

abbrev EDDEVID2_Type := (BitVec 32)

abbrev FCSEIDR_Type := (BitVec 32)

abbrev JIDR_Type := (BitVec 32)

abbrev JMCR_Type := (BitVec 32)

abbrev JOSCR_Type := (BitVec 32)

abbrev ID_AFR0_EL1_Type := (BitVec 64)

abbrev ID_AFR0_Type := (BitVec 32)

abbrev CNTFRQ_EL0_Type := (BitVec 64)

abbrev DBGDTRRX_EL0_Type := (BitVec 64)

abbrev DBGDTRTX_EL0_Type := (BitVec 64)

abbrev HFGITR2_EL2_Type := (BitVec 64)

abbrev ID_AA64AFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64AFR1_EL1_Type := (BitVec 64)

abbrev OSDTRRX_EL1_Type := (BitVec 64)

abbrev OSDTRTX_EL1_Type := (BitVec 64)

abbrev PMEVCNTR_EL0_Type := (BitVec 64)

structure TLBIInfo where
  rec' : TLBIRecord
  shareability : Shareability
  deriving BEq, Inhabited, Repr

abbrev PMEVCNTR_Type := (BitVec 32)

abbrev ICC_AP0R_EL1_Type := (BitVec 64)

abbrev AIDR_EL1_Type := (BitVec 64)

abbrev REVIDR_EL1_Type := (BitVec 64)

abbrev TPIDR_EL2_Type := (BitVec 64)

abbrev ACTLR_EL2_Type := (BitVec 64)

abbrev TPIDR_EL1_Type := (BitVec 64)

abbrev ACTLR_EL1_Type := (BitVec 64)

abbrev AFSR1_EL1_Type := (BitVec 64)

abbrev AMAIR2_EL2_Type := (BitVec 64)

abbrev ICV_AP0R_EL1_Type := (BitVec 64)

abbrev AFSR0_EL3_Type := (BitVec 64)

abbrev AFSR1_EL2_Type := (BitVec 64)

abbrev AFSR0_EL1_Type := (BitVec 64)

abbrev SCXTNUM_EL2_Type := (BitVec 64)

abbrev TPIDR_EL3_Type := (BitVec 64)

abbrev ACTLR_EL3_Type := (BitVec 64)

abbrev AMAIR_EL2_Type := (BitVec 64)

abbrev AMAIR_EL3_Type := (BitVec 64)

abbrev SCXTNUM_EL1_Type := (BitVec 64)

abbrev TPIDRRO_EL0_Type := (BitVec 64)

abbrev AMAIR_EL1_Type := (BitVec 64)

abbrev SCXTNUM_EL0_Type := (BitVec 64)

abbrev TPIDR2_EL0_Type := (BitVec 64)

abbrev SCXTNUM_EL3_Type := (BitVec 64)

abbrev TPIDR_EL0_Type := (BitVec 64)

abbrev HACR_EL2_Type := (BitVec 64)

abbrev AMAIR2_EL3_Type := (BitVec 64)

abbrev AFSR1_EL3_Type := (BitVec 64)

abbrev AFSR0_EL2_Type := (BitVec 64)

abbrev AMAIR2_EL1_Type := (BitVec 64)

abbrev CNTVOFF_Type := (BitVec 64)

abbrev AMEVCNTVOFF0_EL2_Type := (BitVec 64)

abbrev AMEVCNTVOFF1_EL2_Type := (BitVec 64)

abbrev ERXADDR_EL1_Type := (BitVec 64)

abbrev ERXMISC0_EL1_Type := (BitVec 64)

abbrev ERXPFGCDN_EL1_Type := (BitVec 64)

abbrev ERXPFGF_EL1_Type := (BitVec 64)

abbrev ERXMISC1_EL1_Type := (BitVec 64)

abbrev ERXCTLR_EL1_Type := (BitVec 64)

abbrev ERXSTATUS_EL1_Type := (BitVec 64)

abbrev ERXFR_EL1_Type := (BitVec 64)

abbrev ERXMISC3_EL1_Type := (BitVec 64)

abbrev ERXMISC2_EL1_Type := (BitVec 64)

abbrev ERXPFGCTL_EL1_Type := (BitVec 64)

abbrev AIFSR_Type := (BitVec 32)

abbrev HACR_Type := (BitVec 32)

abbrev HACTLR_Type := (BitVec 32)

abbrev TCMTR_Type := (BitVec 32)

abbrev ICV_AP0R_Type := (BitVec 32)

abbrev TPIDRURW_Type := (BitVec 32)

abbrev ICV_AP1R_Type := (BitVec 32)

abbrev ADFSR_Type := (BitVec 32)

abbrev REVIDR_Type := (BitVec 32)

abbrev TPIDRURO_Type := (BitVec 32)

abbrev ACTLR_Type := (BitVec 32)

abbrev ICC_AP1R_Type := (BitVec 32)

abbrev AMAIR0_Type := (BitVec 32)

abbrev HAMAIR0_Type := (BitVec 32)

abbrev AIDR_Type := (BitVec 32)

abbrev HADFSR_Type := (BitVec 32)

abbrev CNTFRQ_Type := (BitVec 32)

abbrev ACTLR2_Type := (BitVec 32)

abbrev HAMAIR1_Type := (BitVec 32)

abbrev HAIFSR_Type := (BitVec 32)

abbrev ICC_AP0R_Type := (BitVec 32)

abbrev TPIDRPRW_Type := (BitVec 32)

abbrev HTPIDR_Type := (BitVec 32)

abbrev AMAIR1_Type := (BitVec 32)

abbrev ERXFR2_Type := (BitVec 32)

abbrev ERXMISC2_Type := (BitVec 32)

abbrev ERXFR_Type := (BitVec 32)

abbrev ERXADDR_Type := (BitVec 32)

abbrev ERXMISC0_Type := (BitVec 32)

abbrev ERXMISC5_Type := (BitVec 32)

abbrev ERXCTLR2_Type := (BitVec 32)

abbrev ERXMISC1_Type := (BitVec 32)

abbrev ERXCTLR_Type := (BitVec 32)

abbrev ERXMISC6_Type := (BitVec 32)

abbrev ERXMISC4_Type := (BitVec 32)

abbrev ERXADDR2_Type := (BitVec 32)

abbrev ERXMISC7_Type := (BitVec 32)

abbrev ERXMISC3_Type := (BitVec 32)

abbrev ERXSTATUS_Type := (BitVec 32)

abbrev HACTLR2_Type := (BitVec 32)

inductive BarrierExt where
  | Barrier_CSDB (_ : Unit)
  deriving Inhabited, BEq, Repr
  open BarrierExt

structure DxB where
  domain : MBReqDomain
  types : MBReqTypes
  nXS : Bool
  deriving BEq, Inhabited, Repr

inductive Barrier where
  | Barrier_DSB (_ : DxB)
  | Barrier_DMB (_ : DxB)
  | Barrier_ISB (_ : Unit)
  | Barrier_SSBB (_ : Unit)
  | Barrier_PSSBB (_ : Unit)
  | Barrier_SB (_ : Unit)
  deriving Inhabited, BEq, Repr
  open Barrier

/-! Fork (structured registers): 1401 registers = gpr : Vector (BitVec 64) 31 + 34 named fields + 22 banks (BitVec_32:406, Vector_BitVec_32_16:8, Vector_BitVec_32_4:8, Vector_BitVec_64_32:7, BitVec_64:465, Vector_BitVec_64_16:6, Vector_BitVec_64_4:11, Vector_BitVec_32_31:2, Bool:331, Int:28, BitVec_1:2, BitVec_56:16, BitVec_16:4, BitVec_4:7, BitVec_128:8, Vector_Bool_32:3, Vector_BitVec_64_64:7, Option_InterruptID:2, BitVec_8:2, BitVec_2:3, Vector_BitVec_64_7:2, Signal:8). -/

/-- Register bank of type `(BitVec 32)` (406 registers). -/
inductive Bank_BitVec_32 : Type where
  | _HACTLR2
  | _ERXSTATUS
  | _ERXMISC3
  | _ERXMISC7
  | _ERXADDR2
  | _ERXMISC4
  | _ERXMISC6
  | _ERXCTLR
  | _ERXMISC1
  | _ERXCTLR2
  | _ERXMISC5
  | _ERXMISC0
  | _ERXADDR
  | _ERXFR
  | _ERXMISC2
  | _ERXFR2
  | _AMAIR1_NS
  | AMAIR1_S
  | _DBGDTRTXint
  | _HTPIDR
  | _DBGDTRRXint
  | _TPIDRPRW_NS
  | TPIDRPRW_S
  | _HAIFSR
  | _HAMAIR1
  | _ACTLR2_NS
  | ACTLR2_S
  | _DBGOSECCR
  | _PMINTENSET
  | _CNTFRQ
  | _HADFSR
  | _AIDR
  | _HAMAIR0
  | _AMAIR0_NS
  | AMAIR0_S
  | _DBGDTRRXext
  | DBGOSLAR
  | _ACTLR_NS
  | ACTLR_S
  | _DBGDTRTXext
  | _TPIDRURO_NS
  | TPIDRURO_S
  | _REVIDR
  | _ADFSR_NS
  | ADFSR_S
  | _TPIDRURW_NS
  | TPIDRURW_S
  | TCMTR
  | _HACTLR
  | _HACR
  | _AIFSR_NS
  | AIFSR_S
  | _PMOVSSET
  | DACR_S
  | _DACR_NS
  | _HMAIR1
  | _HMAIR0
  | _MAIR1_S
  | _MAIR1_NS
  | _MAIR0_S
  | _MAIR0_NS
  | __CNTbase_frequency
  | GICD_TYPER
  | EDDEVARCH
  | CTIDEVARCH
  | CNTFID0
  | CFG_MPIDR
  | AMIIDR
  | AMDEVARCH
  | _PMCEID3
  | _PMCEID2
  | _PMCEID1
  | _PMCEID0
  | _NMRR_NS
  | NMRR_S
  | _MVFR1
  | _MVFR0
  | _MIDR
  | _ID_PFR1
  | _ID_PFR0
  | _ID_MMFR4
  | _ID_MMFR3
  | _ID_MMFR2
  | _ID_MMFR1
  | _ID_MMFR0
  | _ID_ISAR6
  | _ID_ISAR4
  | _ID_ISAR3
  | _ID_ISAR2
  | _ID_ISAR1
  | _ID_DFR0
  | _CLIDR
  | TLBTR
  | FPSID
  | DBGDEVID
  | _VTCR
  | _VPIDR
  | _VMPIDR
  | _TTBCR2_NS
  | TTBCR2_S
  | _TRFCR
  | _RMR
  | _PRRR_NS
  | PRRR_S
  | _PMUSERENR
  | _PMSWINC
  | _PMSELR
  | _MVFR2
  | _MPIDR
  | _ISR
  | _ID_PFR2
  | _ID_MMFR5
  | _ID_ISAR5
  | _ID_ISAR0
  | _ID_DFR1
  | _ID_AFR0
  | _ICV_RPR
  | _ICV_PMR
  | _ICV_IGRPEN1
  | _ICV_IGRPEN0
  | _ICV_IAR1
  | _ICV_IAR0
  | _ICV_HPPIR1
  | _ICV_HPPIR0
  | _ICV_EOIR1
  | _ICV_EOIR0
  | _ICV_DIR
  | _ICV_CTLR
  | _ICV_BPR1
  | _ICV_BPR0
  | _ICH_VTR
  | _ICH_VMCR
  | _ICH_MISR
  | _ICH_HCR
  | _ICH_ELRSR
  | _ICH_EISR
  | _ICC_SRE_S
  | _ICC_SRE_NS
  | _ICC_RPR
  | _ICC_PMR
  | _ICC_IGRPEN1_S
  | _ICC_IGRPEN1_NS
  | _ICC_IGRPEN0
  | _ICC_IAR1
  | _ICC_IAR0
  | _ICC_HSRE
  | _ICC_HPPIR1
  | _ICC_HPPIR0
  | _ICC_EOIR1
  | _ICC_EOIR0
  | _ICC_DIR
  | _ICC_CTLR_S
  | _ICC_CTLR_NS
  | _ICC_BPR1_S
  | _ICC_BPR1_NS
  | _ICC_BPR0
  | _HTRFCR
  | _HTCR
  | _HSTR
  | _HRMR
  | _ERRSELR
  | _ERRIDR
  | _DBGVCR
  | _DBGDCCINT
  | _DBGCLAIMSET
  | _DBGCLAIMCLR
  | _DBGAUTHSTATUS
  | _CTR
  | _CSSELR_NS
  | CSSELR_S
  | _CNTV_CTL
  | _CNTHV_CTL
  | _CNTHVS_CTL
  | _CNTHPS_CTL
  | _CNTHCTL
  | _CCSIDR
  | _CCSIDR2
  | _AMUSERENR
  | _AMCR
  | _AMCNTENSET1
  | _AMCNTENSET0
  | _AMCNTENCLR1
  | _AMCNTENCLR0
  | _AMCGCR
  | _AMCFGR
  | PMVIDSR
  | PMPIDR4
  | PMPIDR3
  | PMPIDR2
  | PMPIDR1
  | PMPIDR0
  | PMMIR
  | PMLSR
  | PMLAR
  | PMITCTRL
  | PMDEVTYPE
  | PMDEVID
  | PMCIDR3
  | PMCIDR2
  | PMCIDR1
  | PMCIDR0
  | PMCGCR0
  | PMAUTHSTATUS
  | JOSCR
  | JMCR
  | JIDR
  | ICC_MSRE
  | ICC_MGRPEN1
  | ICC_MCTLR
  | GITS_STATUSR
  | GITS_PARTIDR
  | GITS_MPIDR
  | GITS_MPAMIDR
  | GITS_IIDR
  | GITS_CTLR
  | GICV_STATUSR
  | GICV_RPR
  | GICV_PMR
  | GICV_IAR
  | GICV_HPPIR
  | GICV_EOIR
  | GICV_DIR
  | GICV_CTLR
  | GICV_BPR
  | GICV_AIAR
  | GICV_AHPPIR
  | GICV_AEOIR
  | GICV_ABPR
  | GICR_WAKER
  | GICR_VSGIR
  | GICR_VSGIPENDR
  | GICR_SYNCR
  | GICR_STATUSR
  | GICR_PARTIDR
  | GICR_MPAMIDR
  | GICR_ISENABLER0
  | GICR_INMIR0
  | GICR_IIDR
  | GICR_CTLR
  | GICM_TYPER
  | GICM_SETSPI_SR
  | GICM_SETSPI_NSR
  | GICM_IIDR
  | GICM_CLRSPI_SR
  | GICM_CLRSPI_NSR
  | GICH_VTR
  | GICH_VMCR
  | GICH_MISR
  | GICH_HCR
  | GICH_ELRSR
  | GICH_EISR
  | GICD_TYPER2
  | GICD_STATUSR
  | GICD_SGIR
  | GICD_SETSPI_SR
  | GICD_SETSPI_NSR
  | GICD_IIDR
  | GICD_CTLR
  | GICD_CLRSPI_SR
  | GICD_CLRSPI_NSR
  | GICC_STATUSR
  | GICC_RPR
  | GICC_PMR
  | GICC_IAR
  | GICC_HPPIR
  | GICC_EOIR
  | GICC_DIR
  | GICC_BPR
  | GICC_AIAR
  | GICC_AHPPIR
  | GICC_AEOIR
  | GICC_ABPR
  | FCSEIDR
  | EDVIDSR
  | EDRCR
  | EDPRSR
  | EDPRCR
  | EDPIDR4
  | EDPIDR3
  | EDPIDR2
  | EDPIDR1
  | EDPIDR0
  | EDLSR
  | EDLAR
  | EDITCTRL
  | EDDEVTYPE
  | EDDEVID2
  | EDDEVID1
  | EDDEVID
  | EDCIDR3
  | EDCIDR2
  | EDCIDR1
  | EDCIDR0
  | DBGWFAR
  | DBGDIDR
  | DBGDEVID2
  | DBGDEVID1
  | CTIPIDR4
  | CTIPIDR3
  | CTIPIDR2
  | CTIPIDR1
  | CTIPIDR0
  | CTILSR
  | CTILAR
  | CTIITCTRL
  | CTIDEVTYPE
  | CTIDEVID2
  | CTIDEVID1
  | CTIDEVID
  | CTIDEVCTL
  | CTICONTROL
  | CTICIDR3
  | CTICIDR2
  | CTICIDR1
  | CTICIDR0
  | CTIAUTHSTATUS
  | CNTSR
  | CNTNSAR
  | CNTID
  | CNTEL0ACR
  | AMPIDR4
  | AMPIDR3
  | AMPIDR2
  | AMPIDR1
  | AMPIDR0
  | AMDEVTYPE
  | AMCIDR3
  | AMCIDR2
  | AMCIDR1
  | AMCIDR0
  | _VDISR
  | _VDFSR
  | _DISR
  | _EDSCR2
  | _CNTKCTL
  | GICC_CTLR
  | CNTSCR
  | CNTCR
  | CNTP_CTL_S
  | _CNTP_CTL_NS
  | _CNTHP_CTL
  | _FPEXC
  | _IFAR_S
  | _IFAR_NS
  | _HCR2
  | _DBGDSCRext
  | _DBGDSCRint
  | IFSR_S
  | _IFSR_NS
  | DFSR_S
  | _DFSR_NS
  | _DFAR_S
  | _DFAR_NS
  | MVBAR
  | _HVBAR
  | _ELR_hyp
  | _HSR
  | _HPFAR
  | _HIFAR
  | _HDFAR
  | CONTEXTIDR_S
  | _CONTEXTIDR_NS
  | TTBCR_S
  | _TTBCR_NS
  | VBAR_S
  | _VBAR_NS
  | EDESR
  | _EDECCR
  | _SPSR_svc
  | SPSR_mon
  | _SPSR_hyp
  | SCTLR_S
  | _SCTLR_NS
  | _HSCTLR
  | _HCR
  | _DBGOSLSR
  | _DBGPRCR
  | _DBGOSDLR
  | NSACR
  | _HCPTR
  | _CPACR
  | _DSPSR2
  | _DSPSR
  | _DLR
  | EDECR
  | _SDER
  | SDCR
  | _PMCNTENSET
  | _PMCCFILTR
  | _PMOVSR
  | _PMINTENCLR
  | _PMCR
  | _PMCNTENCLR
  | _EDSCR
  | _HDCR
  | RVBAR
  | _FPSCR
  | SCR
  | LR_mon
  | SP_mon
  | __ThisInstr
  | SPESampleContextEL2
  | SPESampleContextEL1
  | _DormantCtlReg
  | _ConfigReg
  | __trcclaim_tags
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 32) 16)` (8 registers). -/
inductive Bank_Vector_BitVec_32_16 : Type where
  | _AMEVTYPER1
  | _ICH_LRC
  | _ICH_LR
  | _DBGWVR
  | _DBGWCR
  | _DBGBXVR
  | _DBGBVR
  | _DBGBCR
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 32) 4)` (8 registers). -/
inductive Bank_Vector_BitVec_32_4 : Type where
  | _AMEVTYPER0
  | _ICC_AP0R
  | _ICH_AP0R
  | _ICH_AP1R
  | _ICC_AP1R_NS
  | _ICC_AP1R_S
  | _ICV_AP1R
  | _ICV_AP0R
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 64) 32)` (7 registers). -/
inductive Bank_Vector_BitVec_64_32 : Type where
  | BRBSRC_EL1
  | BRBTGT_EL1
  | BRBINF_EL1
  | PMEVCNTR_EL0
  | SPESampleAddress
  | PMEVTYPER_EL0
  | _Dclone
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 64)` (465 registers). -/
inductive Bank_BitVec_64 : Type where
  | ERXPFGCTL_EL1
  | ERXMISC2_EL1
  | ERXMISC3_EL1
  | ERXGSR_EL1
  | ERXFR_EL1
  | ERXSTATUS_EL1
  | ERXCTLR_EL1
  | ERXMISC1_EL1
  | ERXPFGF_EL1
  | ERXPFGCDN_EL1
  | ERXMISC0_EL1
  | ERXADDR_EL1
  | _CNTV_CVAL
  | _CNTVOFF
  | SPMACCESSR_EL3
  | AMAIR2_EL1
  | AFSR0_EL2
  | AFSR1_EL3
  | AMAIR2_EL3
  | HACR_EL2
  | RNDR
  | SMPRIMAP_EL2
  | RNDRRS
  | TPIDR_EL0
  | SCXTNUM_EL3
  | TPIDR2_EL0
  | SCXTNUM_EL0
  | AMAIR_EL1
  | TPIDRRO_EL0
  | SCXTNUM_EL1
  | AMAIR_EL3
  | AMAIR_EL2
  | ACTLR_EL3
  | TPIDR_EL3
  | PMIAR_EL1
  | SCXTNUM_EL2
  | PMICNTSVR_EL1
  | SPMACCESSR_EL2
  | AFSR0_EL1
  | AFSR1_EL2
  | AFSR0_EL3
  | AMAIR2_EL2
  | PMCCNTSVR_EL1
  | AFSR1_EL1
  | ACTLR_EL1
  | TPIDR_EL1
  | SPMACCESSR_EL1
  | ACTLR_EL2
  | TPIDR_EL2
  | REVIDR_EL1
  | AIDR_EL1
  | _PMCCNTR
  | STACK_LIMIT
  | STACK_BASE
  | HEAP_LIMIT
  | HEAP_BASE
  | _DBGDTR_EL0
  | BRBTGTINJ_EL1
  | BRBSRCINJ_EL1
  | PMSDSFR_EL1
  | PMBPTR_EL1
  | PMCCNTR_EL0
  | ID_AA64PFR0_EL1
  | ID_AA64MMFR1_EL1
  | ID_AA64ISAR1_EL1
  | ID_AA64DFR1_EL1
  | ID_AA64DFR0_EL1
  | SPMSELR_EL0
  | SMPRI_EL1
  | SMIDR_EL1
  | PMZR_EL0
  | PMXEVCNTR_EL0
  | PMUACR_EL1
  | PMSSCR_EL1
  | PMSNEVFR_EL1
  | PMSLATFR_EL1
  | PMSIRR_EL1
  | PMSICR_EL1
  | PMSFCR_EL1
  | PMSEVFR_EL1
  | PMMIR_EL1
  | PMECR_EL1
  | PMBIDR_EL1
  | OSLAR_EL1
  | OSDTRTX_EL1
  | OSDTRRX_EL1
  | MECIDR_EL2
  | MDSELR_EL1
  | LORSA_EL1
  | LORN_EL1
  | LORID_EL1
  | LOREA_EL1
  | LORC_EL1
  | ID_AA64ZFR0_EL1
  | ID_AA64SMFR0_EL1
  | ID_AA64PFR2_EL1
  | ID_AA64PFR1_EL1
  | ID_AA64MMFR4_EL1
  | ID_AA64MMFR3_EL1
  | ID_AA64MMFR2_EL1
  | ID_AA64MMFR0_EL1
  | ID_AA64ISAR2_EL1
  | ID_AA64ISAR0_EL1
  | ID_AA64AFR1_EL1
  | ID_AA64AFR0_EL1
  | ICV_NMIAR1_EL1
  | ICC_SRE_EL3
  | ICC_NMIAR1_EL1
  | ICC_IGRPEN1_EL3
  | ICC_CTLR_EL3
  | HFGWTR_EL2
  | HFGWTR2_EL2
  | HFGRTR_EL2
  | HFGRTR2_EL2
  | HFGITR2_EL2
  | HDFGWTR_EL2
  | HDFGWTR2_EL2
  | HDFGRTR_EL2
  | HDFGRTR2_EL2
  | HAFGRTR_EL2
  | GMID_EL1
  | DCZID_EL0
  | DBGDTRTX_EL0
  | DBGDTRRX_EL0
  | DACR32_EL2
  | CNTV_TVAL_EL0
  | CNTP_TVAL_EL0
  | CNTPS_TVAL_EL1
  | CNTHV_TVAL_EL2
  | CNTHVS_TVAL_EL2
  | CNTHP_TVAL_EL2
  | CNTHPS_TVAL_EL2
  | CNTFRQ_EL0
  | BRBINFINJ_EL1
  | AMCG1IDR_EL0
  | ACCDATA_EL1
  | PMCEID1_EL0
  | PMCEID0_EL0
  | MVFR1_EL1
  | MVFR0_EL1
  | MIDR_EL1
  | ID_PFR1_EL1
  | ID_PFR0_EL1
  | ID_MMFR4_EL1
  | ID_MMFR3_EL1
  | ID_MMFR2_EL1
  | ID_MMFR1_EL1
  | ID_MMFR0_EL1
  | ID_ISAR6_EL1
  | ID_ISAR4_EL1
  | ID_ISAR3_EL1
  | ID_ISAR2_EL1
  | ID_ISAR1_EL1
  | ID_DFR0_EL1
  | VPIDR_EL2
  | VMPIDR_EL2
  | TRFCR_EL1
  | RMR_EL3
  | RMR_EL1
  | PMUSERENR_EL0
  | PMSWINC_EL0
  | PMSELR_EL0
  | _PMOVS
  | _PMINTEN
  | PMINTENSET_EL1
  | _PMCNTEN
  | PAR_S
  | PAR_NS
  | MVFR2_EL1
  | MPIDR_EL1
  | ISR_EL1
  | ID_PFR2_EL1
  | ID_MMFR5_EL1
  | ID_ISAR5_EL1
  | ID_ISAR0_EL1
  | ID_DFR1_EL1
  | ID_AFR0_EL1
  | ICV_RPR_EL1
  | ICV_PMR_EL1
  | ICV_IGRPEN1_EL1
  | ICV_IGRPEN0_EL1
  | ICV_IAR1_EL1
  | ICV_IAR0_EL1
  | ICV_HPPIR1_EL1
  | ICV_HPPIR0_EL1
  | ICV_EOIR1_EL1
  | ICV_EOIR0_EL1
  | ICV_DIR_EL1
  | ICV_CTLR_EL1
  | ICV_BPR1_EL1
  | ICV_BPR0_EL1
  | ICH_VTR_EL2
  | ICH_VMCR_EL2
  | ICH_MISR_EL2
  | ICH_HCR_EL2
  | ICH_ELRSR_EL2
  | ICH_EISR_EL2
  | ICC_SRE_EL1_S
  | ICC_SRE_EL1_NS
  | _ICC_SGI1R
  | ICC_SGI1R_EL1
  | _ICC_SGI0R
  | ICC_SGI0R_EL1
  | ICC_RPR_EL1
  | ICC_IGRPEN1_EL1_S
  | ICC_IGRPEN1_EL1_NS
  | ICC_IGRPEN0_EL1
  | ICC_IAR1_EL1
  | ICC_IAR0_EL1
  | ICC_SRE_EL2
  | ICC_HPPIR1_EL1
  | ICC_HPPIR0_EL1
  | ICC_EOIR1_EL1
  | ICC_EOIR0_EL1
  | ICC_DIR_EL1
  | ICC_CTLR_EL1_S
  | ICC_CTLR_EL1_NS
  | ICC_BPR1_EL1_S
  | ICC_BPR1_EL1_NS
  | ICC_BPR0_EL1
  | _ICC_ASGI1R
  | ICC_ASGI1R_EL1
  | TRFCR_EL2
  | HSTR_EL2
  | RMR_EL2
  | ERRSELR_EL1
  | ERRIDR_EL1
  | DBGVCR32_EL2
  | _DBGDRAR
  | MDRAR_EL1
  | MDCCINT_EL1
  | DBGCLAIMSET_EL1
  | DBGCLAIMCLR_EL1
  | DBGAUTHSTATUS_EL1
  | CSSELR_EL1
  | CCSIDR_EL1
  | CCSIDR2_EL1
  | AMUSERENR_EL0
  | AMCR_EL0
  | AMCNTENSET1_EL0
  | AMCNTENSET0_EL0
  | AMCNTENCLR1_EL0
  | AMCNTENCLR0_EL0
  | AMCGCR_EL0
  | AMCFGR_EL0
  | PMVCIDSR
  | PMPCSR
  | PMPCSCTL
  | PMIIDR
  | PMCFGR
  | GITS_TYPER
  | GITS_SGIR
  | GITS_CWRITER
  | GITS_CREADR
  | GITS_CBASER
  | GICR_VPROPBASER
  | GICR_VPENDBASER
  | GICR_SETLPIR
  | GICR_PROPBASER
  | GICR_PENDBASER
  | GICR_INVLPIR
  | GICR_INVALLR
  | GICR_CLRLPIR
  | EDPFR
  | EDPCSR
  | EDHSR
  | EDDFR1
  | EDDFR
  | EDAA32PFR
  | DBGDSAR
  | RVBAR_EL3
  | RVBAR_EL2
  | RVBAR_EL1
  | VDISR_EL2
  | VSESR_EL2
  | DISR_EL1
  | HFGITR_EL2
  | VNCR_EL2
  | VMECID_A_EL2
  | S2POR_EL1
  | VSTTBR_EL2
  | VSTCR_EL2
  | S2PIR_EL2
  | MECID_RL_A_EL3
  | MECID_P1_EL2
  | MECID_A1_EL2
  | MECID_A0_EL2
  | VMECID_P_EL2
  | MECID_P0_EL2
  | POR_EL0
  | POR_EL3
  | POR_EL2
  | POR_EL1
  | EDWAR
  | VTTBR
  | VTCR_EL2
  | CONTEXTIDR_EL2
  | TFSR_EL3
  | TFSR_EL2
  | TFSR_EL1
  | TFSRE0_EL1
  | RGSR_EL1
  | GCR_EL1
  | APGAKeyLo_EL1
  | APGAKeyHi_EL1
  | APDBKeyLo_EL1
  | APDBKeyHi_EL1
  | APDAKeyLo_EL1
  | APDAKeyHi_EL1
  | APIBKeyLo_EL1
  | APIBKeyHi_EL1
  | APIAKeyLo_EL1
  | APIAKeyHi_EL1
  | TTBR0_EL3
  | SCTLR2_EL3
  | PIR_EL3
  | MAIR_EL3
  | MAIR2_EL3
  | PIRE0_EL2
  | TCR2_EL2
  | PIR_EL2
  | MAIR_EL2
  | MAIR2_EL2
  | TCR2_EL1
  | PIR_EL1
  | PIRE0_EL1
  | MAIR_EL1
  | MAIR2_EL1
  | GPTBR_EL3
  | GPCCR_EL3
  | CNTKCTL_EL1
  | CNTPS_CVAL_EL1
  | CNTPS_CTL_EL1
  | CNTHV_CVAL_EL2
  | CNTHV_CTL_EL2
  | CNTHVS_CVAL_EL2
  | CNTHVS_CTL_EL2
  | CNTHPS_CVAL_EL2
  | CNTHPS_CTL_EL2
  | CNTV_CVAL_EL0
  | CNTV_CTL_EL0
  | CNTP_CVAL_S
  | _CNTP_CVAL_NS
  | CNTP_CVAL_EL0
  | CNTP_CTL_EL0
  | _CNTHP_CVAL
  | CNTHP_CVAL_EL2
  | CNTHP_CTL_EL2
  | FPEXC32_EL2
  | SCTLR2_EL2
  | SCTLR2_EL1
  | IFSR32_EL2
  | TTBR1_S
  | TTBR1_NS
  | HTTBR
  | TTBR0_S
  | TTBR0_NS
  | CONTEXTIDR_EL1
  | CLIDR_EL1
  | MPAMSM_EL1
  | MPAM0_EL1
  | MPAMVPM7_EL2
  | MPAMVPM6_EL2
  | MPAMVPM5_EL2
  | MPAMVPM4_EL2
  | MPAMVPM3_EL2
  | MPAMVPM2_EL2
  | MPAMVPM1_EL2
  | MPAMVPMV_EL2
  | MPAMVPM0_EL2
  | MPAMHCR_EL2
  | MPAMIDR_EL1
  | _MPAM1_EL1
  | _MPAM3_EL3
  | MPAM2_EL2
  | HCRX_EL2
  | GCSCRE0_EL1
  | VBAR_EL3
  | VBAR_EL2
  | VBAR_EL1
  | OSECCR_EL1
  | SPSR_und
  | SPSR_irq
  | SPSR_fiq
  | SPSR_abt
  | SPSR_EL3
  | SPSR_EL2
  | SPSR_EL1
  | ELR_EL3
  | ELR_EL2
  | ELR_EL1
  | PFAR_EL2
  | PFAR_EL1
  | MFAR_EL3
  | HPFAR_EL2
  | FAR_EL3
  | FAR_EL2
  | FAR_EL1
  | ESR_EL3
  | ESR_EL2
  | ESR_EL1
  | SCTLR_EL3
  | SCTLR_EL1
  | SCTLR_EL2
  | OSLSR_EL1
  | MDSCR_EL1
  | GCSCR_EL3
  | GCSCR_EL2
  | GCSCR_EL1
  | DBGPRCR_EL1
  | OSDLR_EL1
  | CPTR_EL3
  | CPTR_EL2
  | CPACR_EL1
  | GCSPR_EL3
  | GCSPR_EL2
  | GCSPR_EL1
  | GCSPR_EL0
  | SMCR_EL3
  | SMCR_EL2
  | SMCR_EL1
  | ZCR_EL3
  | ZCR_EL2
  | ZCR_EL1
  | PMBSR_EL1
  | PMBLIMITR_EL1
  | PMSCR_EL2
  | PMSCR_EL1
  | PMSIDR_EL1
  | BRBIDR0_EL1
  | TCR_EL3
  | TCR_EL2
  | TCR_EL1
  | DSPSR_EL0
  | DLR_EL0
  | CFG_RVBAR
  | CNTHCTL_EL2
  | CNTVOFF_EL2
  | CNTPOFF_EL2
  | BRBTS_EL1
  | BRBFCR_EL1
  | BRBCR_EL2
  | BRBCR_EL1
  | PMOVSSET_EL0
  | PMICNTR_EL0
  | _SDER32_EL3
  | SDER32_EL2
  | PMICFILTR_EL0
  | PMCNTENSET_EL0
  | PMCCFILTR_EL0
  | MDCR_EL3
  | PMOVSCLR_EL0
  | PMINTENCLR_EL1
  | PMCR_EL0
  | PMCNTENCLR_EL0
  | MDCCSR_EL0
  | MDCR_EL2
  | CTR_EL0
  | SCR_EL3
  | HCR_EL2
  | sp_rel_access_pc
  | SPESampleEvents
  | SPESampleTimestamp
  | SPESamplePreviousBranchAddress
  | ICC_PMR_EL1
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 64) 16)` (6 registers). -/
inductive Bank_Vector_BitVec_64_16 : Type where
  | AMEVTYPER1_EL0
  | AMEVCNTVOFF1_EL2
  | _AMEVCNTR1
  | AMEVCNTVOFF0_EL2
  | AMEVCNTR1_EL0
  | ICH_LR_EL2
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 64) 4)` (11 registers). -/
inductive Bank_Vector_BitVec_64_4 : Type where
  | _AMEVCNTR0_EL0
  | AMEVCNTR0
  | ICV_AP1R_EL1
  | ICV_AP0R_EL1
  | ICC_AP1R_EL1_NS
  | ICC_AP1R_EL1_S
  | ICH_AP0R_EL2
  | ICH_AP1R_EL2
  | ICC_AP0R_EL1
  | AMEVTYPER0_EL0
  | ERRnFR
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 32) 31)` (2 registers). -/
inductive Bank_Vector_BitVec_32_31 : Type where
  | _PMEVCNTR
  | _PMEVTYPER
  deriving DecidableEq, Repr

/-- Register bank of type `Bool` (331 registers). -/
inductive Bank_Bool : Type where
  | __has_spe_pseudo_cycles
  | __mops_forward_copy
  | __trickbox_enabled
  | __ignore_rvbar_in_aarch32
  | __unpred_tsize_aborts
  | __syncAbortOnDeviceWrite
  | __syncAbortOnWriteNormNonCache
  | __syncAbortOnWriteNormCache
  | __syncAbortOnTTWNonCache
  | __syncAbortOnTTWCache
  | __syncAbortOnPrefetch
  | __syncAbortOnSoWrite
  | __syncAbortOnSoRead
  | __syncAbortOnDeviceRead
  | __syncAbortOnReadNormNonCache
  | __syncAbortOnReadNormCache
  | __mpam_has_altsp
  | __tlb_enabled
  | __mpam_has_hcr
  | C47_IMPDEF_TRANSACTIONAL_SYSREG_ACCESS
  | C40_IMPDEF_BOOL_9
  | C40_IMPDEF_BOOL_6
  | C40_IMPDEF_BOOL_5
  | C40_IMPDEF_BOOL_4
  | C40_IMPDEF_BOOL_3
  | C40_IMPDEF_BOOL_2
  | C40_IMPDEF_BOOL_11
  | C40_IMPDEF_BOOL_1
  | C40_IMPDEF_BOOL_0
  | __sme_only
  | __setg_mops_option_a_supported
  | __set_mops_option_a_supported
  | __isb_is_branch
  | __has_sme_priority_control
  | __feat_rpres
  | __empam_tidr_implemented
  | __empam_sdeflt_implemented
  | __empam_force_ns_implemented
  | __empam_force_ns_RAO
  | __cpyf_mops_option_a_supported
  | __cpy_mops_option_a_supported
  | __apply_effective_shareability
  | __highest_el_aarch32
  | __ExclusiveMonitorSet
  | __InstructionStep
  | __last_branch_valid
  | __SPE_LFSR_initialized
  | SPESampleTimestampValid
  | SPESampleSubclassValid
  | SPESampleDataSourceValid
  | SPESamplePreviousBranchAddressValid
  | SPESampleInstIsNV2
  | SPESampleContextEL2Valid
  | SPESampleContextEL1Valid
  | SPESampleInFlight
  | InGuardedPage
  | IsWFEsleep
  | IsWFIsleep
  | v9Ap4_IMPLEMENTED
  | v9Ap3_IMPLEMENTED
  | v9Ap2_IMPLEMENTED
  | v9Ap1_IMPLEMENTED
  | v9Ap0_IMPLEMENTED
  | v8Ap9_IMPLEMENTED
  | v8Ap8_IMPLEMENTED
  | v8Ap7_IMPLEMENTED
  | v8Ap6_IMPLEMENTED
  | v8Ap5_IMPLEMENTED
  | v8Ap4_IMPLEMENTED
  | v8Ap3_IMPLEMENTED
  | v8Ap2_IMPLEMENTED
  | v8Ap1_IMPLEMENTED
  | v8Ap0_IMPLEMENTED
  | FEAT_TRBE_MPAM_IMPLEMENTED
  | FEAT_TRBE_EXT_IMPLEMENTED
  | FEAT_SYSREG128_IMPLEMENTED
  | FEAT_SYSINSTR128_IMPLEMENTED
  | FEAT_SVE_B16B16_IMPLEMENTED
  | FEAT_SVE2p1_IMPLEMENTED
  | FEAT_SME_F16F16_IMPLEMENTED
  | FEAT_SME2p1_IMPLEMENTED
  | FEAT_SEBEP_IMPLEMENTED
  | FEAT_LVA3_IMPLEMENTED
  | FEAT_LSE128_IMPLEMENTED
  | FEAT_ITE_IMPLEMENTED
  | FEAT_GCS_IMPLEMENTED
  | FEAT_ETEv1p3_IMPLEMENTED
  | FEAT_EBEP_IMPLEMENTED
  | FEAT_D128_IMPLEMENTED
  | FEAT_CHK_IMPLEMENTED
  | FEAT_ABLE_IMPLEMENTED
  | FEAT_SME2_IMPLEMENTED
  | FEAT_MEC_IMPLEMENTED
  | FEAT_BRBEv1p1_IMPLEMENTED
  | FEAT_SME_I16I64_IMPLEMENTED
  | FEAT_SME_FA64_IMPLEMENTED
  | FEAT_SME_F64F64_IMPLEMENTED
  | FEAT_SME_IMPLEMENTED
  | FEAT_RME_IMPLEMENTED
  | FEAT_ETEv1p2_IMPLEMENTED
  | FEAT_BRBE_IMPLEMENTED
  | FEAT_ETEv1p1_IMPLEMENTED
  | FEAT_TRBE_IMPLEMENTED
  | FEAT_TME_IMPLEMENTED
  | FEAT_SVE_SM4_IMPLEMENTED
  | FEAT_SVE_SHA3_IMPLEMENTED
  | FEAT_SVE_PMULL128_IMPLEMENTED
  | FEAT_SVE_BitPerm_IMPLEMENTED
  | FEAT_SVE_AES_IMPLEMENTED
  | FEAT_SVE2_IMPLEMENTED
  | FEAT_ETE_IMPLEMENTED
  | FEAT_DoPD_IMPLEMENTED
  | FEAT_THE_IMPLEMENTED
  | FEAT_SPMU_IMPLEMENTED
  | FEAT_SPEv1p4_IMPLEMENTED
  | FEAT_SPE_FDS_IMPLEMENTED
  | FEAT_SPE_CRR_IMPLEMENTED
  | FEAT_SPECRES2_IMPLEMENTED
  | FEAT_S2POE_IMPLEMENTED
  | FEAT_S2PIE_IMPLEMENTED
  | FEAT_S1POE_IMPLEMENTED
  | FEAT_S1PIE_IMPLEMENTED
  | FEAT_RPRFM_IMPLEMENTED
  | FEAT_RASv2_IMPLEMENTED
  | FEAT_RASSAv2_IMPLEMENTED
  | FEAT_PRFMSLC_IMPLEMENTED
  | FEAT_PMUv3p9_IMPLEMENTED
  | FEAT_PMUv3_SS_IMPLEMENTED
  | FEAT_PMUv3_ICNTR_IMPLEMENTED
  | FEAT_PMUv3_EDGE_IMPLEMENTED
  | FEAT_PFAR_IMPLEMENTED
  | FEAT_PCSRv8p9_IMPLEMENTED
  | FEAT_MTE_TAGGED_FAR_IMPLEMENTED
  | FEAT_MTE_STORE_ONLY_IMPLEMENTED
  | FEAT_MTE_PERM_IMPLEMENTED
  | FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED
  | FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED
  | FEAT_MTE_ASYNC_IMPLEMENTED
  | FEAT_MTE_ASYM_FAULT_IMPLEMENTED
  | FEAT_MTE4_IMPLEMENTED
  | FEAT_LRCPC3_IMPLEMENTED
  | FEAT_HAFT_IMPLEMENTED
  | FEAT_FGT2_IMPLEMENTED
  | FEAT_ECBHB_IMPLEMENTED
  | FEAT_DoubleFault2_IMPLEMENTED
  | FEAT_Debugv8p9_IMPLEMENTED
  | FEAT_CSSC_IMPLEMENTED
  | FEAT_CLRBHB_IMPLEMENTED
  | FEAT_ANERR_IMPLEMENTED
  | FEAT_AIE_IMPLEMENTED
  | FEAT_ADERR_IMPLEMENTED
  | FEAT_TIDCP1_IMPLEMENTED
  | FEAT_TCR2_IMPLEMENTED
  | FEAT_SPEv1p3_IMPLEMENTED
  | FEAT_SCTLR2_IMPLEMENTED
  | FEAT_PMUv3p8_IMPLEMENTED
  | FEAT_PMUv3_TH_IMPLEMENTED
  | FEAT_PMUv3_EXT64_IMPLEMENTED
  | FEAT_NMI_IMPLEMENTED
  | FEAT_MOPS_IMPLEMENTED
  | FEAT_HBC_IMPLEMENTED
  | FEAT_GICv3_NMI_IMPLEMENTED
  | FEAT_Debugv8p8_IMPLEMENTED
  | FEAT_CMOW_IMPLEMENTED
  | FEAT_XS_IMPLEMENTED
  | FEAT_WFxT_IMPLEMENTED
  | FEAT_SPEv1p2_IMPLEMENTED
  | FEAT_RPRES_IMPLEMENTED
  | FEAT_PMUv3p7_IMPLEMENTED
  | FEAT_PAN3_IMPLEMENTED
  | FEAT_MTE3_IMPLEMENTED
  | FEAT_LS64_V_IMPLEMENTED
  | FEAT_LS64_ACCDATA_IMPLEMENTED
  | FEAT_LS64_IMPLEMENTED
  | FEAT_LPA2_IMPLEMENTED
  | FEAT_HCX_IMPLEMENTED
  | FEAT_EBF16_IMPLEMENTED
  | FEAT_AFP_IMPLEMENTED
  | FEAT_TWED_IMPLEMENTED
  | FEAT_PAuth2_IMPLEMENTED
  | FEAT_MTPMU_IMPLEMENTED
  | FEAT_MPAMv1p1_IMPLEMENTED
  | FEAT_MPAMv0p1_IMPLEMENTED
  | FEAT_HPMN0_IMPLEMENTED
  | FEAT_FGT_IMPLEMENTED
  | FEAT_ECV_IMPLEMENTED
  | FEAT_DGH_IMPLEMENTED
  | FEAT_BF16_IMPLEMENTED
  | FEAT_AMUv1p1_IMPLEMENTED
  | FEAT_SSBS2_IMPLEMENTED
  | FEAT_SSBS_IMPLEMENTED
  | FEAT_SPECRES_IMPLEMENTED
  | FEAT_SB_IMPLEMENTED
  | FEAT_RNG_TRAP_IMPLEMENTED
  | FEAT_RNG_IMPLEMENTED
  | FEAT_PMUv3p5_IMPLEMENTED
  | FEAT_MTE2_IMPLEMENTED
  | FEAT_MTE_IMPLEMENTED
  | FEAT_GTG_IMPLEMENTED
  | FEAT_FlagM2_IMPLEMENTED
  | FEAT_FRINTTS_IMPLEMENTED
  | FEAT_ExS_IMPLEMENTED
  | FEAT_EVT_IMPLEMENTED
  | FEAT_E0PD_IMPLEMENTED
  | FEAT_DPB2_IMPLEMENTED
  | FEAT_CSV3_IMPLEMENTED
  | FEAT_CSV2_IMPLEMENTED
  | FEAT_BTI_IMPLEMENTED
  | FEAT_TTST_IMPLEMENTED
  | FEAT_TTL_IMPLEMENTED
  | FEAT_TRF_IMPLEMENTED
  | FEAT_TLBIRANGE_IMPLEMENTED
  | FEAT_TLBIOS_IMPLEMENTED
  | FEAT_SEL2_IMPLEMENTED
  | FEAT_S2FWB_IMPLEMENTED
  | FEAT_RASv1p1_IMPLEMENTED
  | FEAT_RASSAv1p1_IMPLEMENTED
  | FEAT_PMUv3p4_IMPLEMENTED
  | FEAT_NV2_IMPLEMENTED
  | FEAT_LSE2_IMPLEMENTED
  | FEAT_LRCPC2_IMPLEMENTED
  | FEAT_IDST_IMPLEMENTED
  | FEAT_FlagM_IMPLEMENTED
  | FEAT_FHM_IMPLEMENTED
  | FEAT_DoubleFault_IMPLEMENTED
  | FEAT_DotProd_IMPLEMENTED
  | FEAT_Debugv8p4_IMPLEMENTED
  | FEAT_DIT_IMPLEMENTED
  | FEAT_CNTSC_IMPLEMENTED
  | FEAT_BBM_IMPLEMENTED
  | FEAT_AMUv1_IMPLEMENTED
  | FEAT_SPEv1p1_IMPLEMENTED
  | FEAT_PAuth_IMPLEMENTED
  | FEAT_PACQARMA5_IMPLEMENTED
  | FEAT_PACQARMA3_IMPLEMENTED
  | FEAT_PACIMP_IMPLEMENTED
  | FEAT_NV_IMPLEMENTED
  | FEAT_LRCPC_IMPLEMENTED
  | FEAT_JSCVT_IMPLEMENTED
  | FEAT_FPACCOMBINE_IMPLEMENTED
  | FEAT_FPAC_IMPLEMENTED
  | FEAT_FCMA_IMPLEMENTED
  | FEAT_EPAC_IMPLEMENTED
  | FEAT_CONSTPACFIELD_IMPLEMENTED
  | FEAT_CCIDX_IMPLEMENTED
  | FEAT_XNX_IMPLEMENTED
  | FEAT_VPIPT_IMPLEMENTED
  | FEAT_UAO_IMPLEMENTED
  | FEAT_TTCNP_IMPLEMENTED
  | FEAT_SVE_IMPLEMENTED
  | FEAT_SPE_IMPLEMENTED
  | FEAT_SM4_IMPLEMENTED
  | FEAT_SM3_IMPLEMENTED
  | FEAT_SHA512_IMPLEMENTED
  | FEAT_SHA3_IMPLEMENTED
  | FEAT_RAS_IMPLEMENTED
  | FEAT_PCSRv8p2_IMPLEMENTED
  | FEAT_PAN2_IMPLEMENTED
  | FEAT_MPAM_IMPLEMENTED
  | FEAT_LVA_IMPLEMENTED
  | FEAT_LSMAOC_IMPLEMENTED
  | FEAT_LPA_IMPLEMENTED
  | FEAT_IESB_IMPLEMENTED
  | FEAT_I8MM_IMPLEMENTED
  | FEAT_HPDS2_IMPLEMENTED
  | FEAT_FP16_IMPLEMENTED
  | FEAT_F64MM_IMPLEMENTED
  | FEAT_F32MM_IMPLEMENTED
  | FEAT_EDHSR_IMPLEMENTED
  | FEAT_Debugv8p2_IMPLEMENTED
  | FEAT_DPB_IMPLEMENTED
  | FEAT_ASMv8p2_IMPLEMENTED
  | FEAT_AA32I8MM_IMPLEMENTED
  | FEAT_AA32HPD_IMPLEMENTED
  | FEAT_AA32BF16_IMPLEMENTED
  | FEAT_VMID16_IMPLEMENTED
  | FEAT_VHE_IMPLEMENTED
  | FEAT_RDM_IMPLEMENTED
  | FEAT_PMUv3p1_IMPLEMENTED
  | FEAT_PAN_IMPLEMENTED
  | FEAT_LSE_IMPLEMENTED
  | FEAT_LOR_IMPLEMENTED
  | FEAT_HPDS_IMPLEMENTED
  | FEAT_HAFDBS_IMPLEMENTED
  | FEAT_Debugv8p1_IMPLEMENTED
  | FEAT_CRC32_IMPLEMENTED
  | FEAT_nTLBPA_IMPLEMENTED
  | FEAT_TRC_SR_IMPLEMENTED
  | FEAT_TRC_EXT_IMPLEMENTED
  | FEAT_SHA256_IMPLEMENTED
  | FEAT_SHA1_IMPLEMENTED
  | FEAT_PMUv3_EXT32_IMPLEMENTED
  | FEAT_PMUv3_EXT_IMPLEMENTED
  | FEAT_PMUv3_IMPLEMENTED
  | FEAT_PMULL_IMPLEMENTED
  | FEAT_PCSRv8_IMPLEMENTED
  | FEAT_IVIPT_IMPLEMENTED
  | FEAT_GICv4p1_IMPLEMENTED
  | FEAT_GICv4_IMPLEMENTED
  | FEAT_GICv3p1_IMPLEMENTED
  | FEAT_GICv3_TDIR_IMPLEMENTED
  | FEAT_GICv3_LEGACY_IMPLEMENTED
  | FEAT_GICv3_IMPLEMENTED
  | FEAT_FP_IMPLEMENTED
  | FEAT_ETS2_IMPLEMENTED
  | FEAT_ETMv4p6_IMPLEMENTED
  | FEAT_ETMv4p5_IMPLEMENTED
  | FEAT_ETMv4p4_IMPLEMENTED
  | FEAT_ETMv4p3_IMPLEMENTED
  | FEAT_ETMv4p2_IMPLEMENTED
  | FEAT_ETMv4p1_IMPLEMENTED
  | FEAT_ETMv4_IMPLEMENTED
  | FEAT_DoubleLock_IMPLEMENTED
  | FEAT_CSV2_3_IMPLEMENTED
  | FEAT_CSV2_2_IMPLEMENTED
  | FEAT_CSV2_1p2_IMPLEMENTED
  | FEAT_CSV2_1p1_IMPLEMENTED
  | FEAT_AdvSIMD_IMPLEMENTED
  | FEAT_AES_IMPLEMENTED
  | FEAT_EL3_IMPLEMENTED
  | FEAT_EL2_IMPLEMENTED
  | FEAT_EL1_IMPLEMENTED
  | FEAT_EL0_IMPLEMENTED
  | FEAT_AA64EL3_IMPLEMENTED
  | FEAT_AA64EL2_IMPLEMENTED
  | FEAT_AA64EL1_IMPLEMENTED
  | FEAT_AA64EL0_IMPLEMENTED
  | FEAT_AA32EL3_IMPLEMENTED
  | FEAT_AA32EL2_IMPLEMENTED
  | FEAT_AA32EL1_IMPLEMENTED
  | FEAT_AA32EL0_IMPLEMENTED
  deriving DecidableEq, Repr

/-- Register bank of type `Int` (28 registers). -/
inductive Bank_Int : Type where
  | SMCR_EL3_LEN_VALUE
  | CPTR_EL3_ESM_VALUE
  | CPTR_EL3_EZ_VALUE
  | ZCR_EL3_LEN_VALUE
  | __supported_va_size
  | __gmid_log2_block_size
  | __dczid_log2_block_size
  | __supported_pa_size
  | __max_implemented_sveveclen
  | __max_implemented_smeveclen
  | __has_sve_extended_bf16
  | __block_bbm_implemented
  | __last_cycle_count
  | SPERecordSize
  | __clock_divider
  | __cycle_count
  | NUM_GIC_LIST_REGS
  | NUM_GIC_PRIORITY_BITS
  | NUM_GIC_PREEMPTION_BITS
  | NUM_BRBE_RECORDS
  | NUM_PMU_COUNTERS
  | NUM_AMU_CG1_MONITORS
  | NUM_AMU_CG0_MONITORS
  | NUM_AMU_COUNTER_GROUPS
  | __num_ctx_breakpoints
  | NUM_WATCHPOINTS
  | NUM_BREAKPOINTS
  | SEE
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 1)` (2 registers). -/
inductive Bank_BitVec_1 : Type where
  | CFG_RMR_AA64
  | EventRegister
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 56)` (16 registers). -/
inductive Bank_BitVec_56 : Type where
  | __DBG_ROM_ADDR
  | __PMUBase
  | __GICITSControlBase
  | __GICDistBase
  | __GICCPUInterfaceBase
  | __ExtDebugBase
  | __CNTControlBase
  | __CTIBase
  | __ETEBase
  | __VLPI_base
  | __SGI_base
  | __RD_base
  | __CNTCTLBase
  | __CNTEL0BaseN
  | __CNTBaseN
  | __CNTReadBase
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 16)` (4 registers). -/
inductive Bank_BitVec_16 : Type where
  | __g1_activity_monitor_offset_implemented
  | __g1_activity_monitor_implemented
  | __mpam_partid_max
  | SPESampleDataSource
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 4)` (7 registers). -/
inductive Bank_BitVec_4 : Type where
  | __rme_l0gptsz
  | __mecid_width
  | __exclusive_granule_size
  | __mte_implemented
  | __mpam_major
  | __mpam_frac
  | __currentCond
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 128)` (8 registers). -/
inductive Bank_BitVec_128 : Type where
  | _PAR_EL1
  | RCWSMASK_EL1
  | RCWMASK_EL1
  | _VTTBR_EL2
  | TTBR1_EL2
  | _TTBR1_EL1
  | _TTBR0_EL2
  | _TTBR0_EL1
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector Bool 32)` (3 registers). -/
inductive Bank_Vector_Bool_32 : Type where
  | SPESampleCounterValid
  | SPESampleCounterPending
  | SPESampleAddressValid
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 64) 64)` (7 registers). -/
inductive Bank_Vector_BitVec_64_64 : Type where
  | DBGWVR_EL1
  | DBGWCR_EL1
  | DBGBVR_EL1
  | DBGBCR_EL1
  | Records_TGT
  | Records_SRC
  | Records_INF
  deriving DecidableEq, Repr

/-- Register bank of type `(Option InterruptID)` (2 registers). -/
inductive Bank_Option_InterruptID : Type where
  | __GIC_Pending
  | __GIC_Active
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 8)` (2 registers). -/
inductive Bank_BitVec_8 : Type where
  | __mpam_pmg_max
  | SPESampleSubclass
  deriving DecidableEq, Repr

/-- Register bank of type `(BitVec 2)` (3 registers). -/
inductive Bank_BitVec_2 : Type where
  | __impdef_TG1
  | __impdef_TG0
  | SPESampleClass
  deriving DecidableEq, Repr

/-- Register bank of type `(Vector (BitVec 64) 7)` (2 registers). -/
inductive Bank_Vector_BitVec_64_7 : Type where
  | __DCACHE_CCSIDR_RESET
  | __ICACHE_CCSIDR_RESET
  deriving DecidableEq, Repr

/-- Register bank of type `Signal` (8 registers). -/
inductive Bank_Signal : Type where
  | RTPIDEN
  | RLPIDEN
  | SPNIDEN
  | SPIDEN
  | NIDEN
  | DBGEN
  | CP15SDISABLE2
  | CP15SDISABLE
  deriving DecidableEq, Repr

/-- The register file: named fields for the architectural core and for singly-typed registers,
one total map per bank of same-typed registers. -/
structure Regs : Type where
  gpr : Vector (BitVec 64) 31
  __emulator_termination_opcode : (Option (BitVec 32))
  PMEVCNTSVR_EL1 : (Vector (BitVec 64) 31)
  SPESampleCounter : (Vector Int 32)
  SPERecordData : (Vector (BitVec 8) 64)
  SP_EL3 : (BitVec 64)
  SP_EL2 : (BitVec 64)
  SP_EL1 : (BitVec 64)
  SP_EL0 : (BitVec 64)
  __mpam_vpmr_max : (BitVec 3)
  __BranchTaken : Bool
  Branchtypetaken : BranchType
  __ThisInstrEnc : __InstrEnc
  __SPE_LFSR : (BitVec 24)
  SPESampleOpType : OpType
  TSTATE : TMState
  FPSR : (BitVec 64)
  FPCR : (BitVec 64)
  _ZT0 : (BitVec 512)
  _ZA : (Vector (BitVec 2048) 256)
  _FFR : (BitVec 256)
  _P : (Vector (BitVec 256) 16)
  _Z : (Vector (BitVec 2048) 32)
  BTypeCompatible : Bool
  BTypeNext : (BitVec 2)
  RC : (Vector (BitVec 64) 5)
  PhysicalCount : (BitVec 88)
  _PC : (BitVec 64)
  ShouldAdvanceSS : Bool
  ShouldAdvanceIT : Bool
  PSTATE : ProcState
  PMULastThresholdValue : (Vector Bool 31)
  PMUEventAccumulator : (Vector Int 31)
  VariantImplemented : (Vector Bool 16)
  FeatureImpl : (Vector Bool 259)
  bank_BitVec_32 : RegMap Bank_BitVec_32 (BitVec 32)
  bank_Vector_BitVec_32_16 : RegMap Bank_Vector_BitVec_32_16 (Vector (BitVec 32) 16)
  bank_Vector_BitVec_32_4 : RegMap Bank_Vector_BitVec_32_4 (Vector (BitVec 32) 4)
  bank_Vector_BitVec_64_32 : RegMap Bank_Vector_BitVec_64_32 (Vector (BitVec 64) 32)
  bank_BitVec_64 : RegMap Bank_BitVec_64 (BitVec 64)
  bank_Vector_BitVec_64_16 : RegMap Bank_Vector_BitVec_64_16 (Vector (BitVec 64) 16)
  bank_Vector_BitVec_64_4 : RegMap Bank_Vector_BitVec_64_4 (Vector (BitVec 64) 4)
  bank_Vector_BitVec_32_31 : RegMap Bank_Vector_BitVec_32_31 (Vector (BitVec 32) 31)
  bank_Bool : RegMap Bank_Bool Bool
  bank_Int : RegMap Bank_Int Int
  bank_BitVec_1 : RegMap Bank_BitVec_1 (BitVec 1)
  bank_BitVec_56 : RegMap Bank_BitVec_56 (BitVec 56)
  bank_BitVec_16 : RegMap Bank_BitVec_16 (BitVec 16)
  bank_BitVec_4 : RegMap Bank_BitVec_4 (BitVec 4)
  bank_BitVec_128 : RegMap Bank_BitVec_128 (BitVec 128)
  bank_Vector_Bool_32 : RegMap Bank_Vector_Bool_32 (Vector Bool 32)
  bank_Vector_BitVec_64_64 : RegMap Bank_Vector_BitVec_64_64 (Vector (BitVec 64) 64)
  bank_Option_InterruptID : RegMap Bank_Option_InterruptID (Option InterruptID)
  bank_BitVec_8 : RegMap Bank_BitVec_8 (BitVec 8)
  bank_BitVec_2 : RegMap Bank_BitVec_2 (BitVec 2)
  bank_Vector_BitVec_64_7 : RegMap Bank_Vector_BitVec_64_7 (Vector (BitVec 64) 7)
  bank_Signal : RegMap Bank_Signal Signal
  deriving Inhabited

namespace Regs

/-- Typed reference to element `i` of the register vector `gpr` (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28 R29 R30). -/
def ref_gpr (i : Nat) (h : i < 31) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.gpr[i]'h
  set v r := { r with gpr := r.gpr.set i v h }
@[simp] theorem ref_gpr_get (i : Nat) (h : i < 31) (r : Regs) : (ref_gpr i h).get r = r.gpr[i]'h := rfl
@[simp] theorem ref_gpr_set (i : Nat) (h : i < 31) (v : (BitVec 64)) (r : Regs) :
    (ref_gpr i h).set v r = { r with gpr := r.gpr.set i v h } := rfl
@[simp] theorem ref_gpr_get_set_same (i : Nat) (h : i < 31) (v : (BitVec 64)) (r : Regs) :
    (ref_gpr i h).get ((ref_gpr i h).set v r) = v := Vector.getElem_set_self h
@[simp] theorem ref_gpr_get_set_ne {i i' : Nat} (h : i < 31) (h' : i' < 31) (v : (BitVec 64)) (r : Regs) (hne : i' ≠ i) :
    (ref_gpr i' h').get ((ref_gpr i h).set v r) = (ref_gpr i' h').get r :=
  Vector.getElem_set_ne h h' (Ne.symm hne)

/-- Typed reference to register `k` of bank `BitVec_32`. -/
def ref_BitVec_32 (k : Bank_BitVec_32) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) where
  get r := r.bank_BitVec_32 k
  set v r := { r with bank_BitVec_32 := RegMap.set r.bank_BitVec_32 k v }
@[simp] theorem ref_BitVec_32_get (k : Bank_BitVec_32) (r : Regs) : (ref_BitVec_32 k).get r = r.bank_BitVec_32 k := rfl
@[simp] theorem ref_BitVec_32_set (k : Bank_BitVec_32) (v : (BitVec 32)) (r : Regs) :
    (ref_BitVec_32 k).set v r = { r with bank_BitVec_32 := RegMap.set r.bank_BitVec_32 k v } := rfl
@[simp] theorem ref_BitVec_32_get_set_same (k : Bank_BitVec_32) (v : (BitVec 32)) (r : Regs) :
    (ref_BitVec_32 k).get ((ref_BitVec_32 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_32_get_set_ne {k k' : Bank_BitVec_32} (v : (BitVec 32)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_32 k').get ((ref_BitVec_32 k).set v r) = (ref_BitVec_32 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_32_16`. -/
def ref_Vector_BitVec_32_16 (k : Bank_Vector_BitVec_32_16) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) where
  get r := r.bank_Vector_BitVec_32_16 k
  set v r := { r with bank_Vector_BitVec_32_16 := RegMap.set r.bank_Vector_BitVec_32_16 k v }
@[simp] theorem ref_Vector_BitVec_32_16_get (k : Bank_Vector_BitVec_32_16) (r : Regs) : (ref_Vector_BitVec_32_16 k).get r = r.bank_Vector_BitVec_32_16 k := rfl
@[simp] theorem ref_Vector_BitVec_32_16_set (k : Bank_Vector_BitVec_32_16) (v : (Vector (BitVec 32) 16)) (r : Regs) :
    (ref_Vector_BitVec_32_16 k).set v r = { r with bank_Vector_BitVec_32_16 := RegMap.set r.bank_Vector_BitVec_32_16 k v } := rfl
@[simp] theorem ref_Vector_BitVec_32_16_get_set_same (k : Bank_Vector_BitVec_32_16) (v : (Vector (BitVec 32) 16)) (r : Regs) :
    (ref_Vector_BitVec_32_16 k).get ((ref_Vector_BitVec_32_16 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_32_16_get_set_ne {k k' : Bank_Vector_BitVec_32_16} (v : (Vector (BitVec 32) 16)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_32_16 k').get ((ref_Vector_BitVec_32_16 k).set v r) = (ref_Vector_BitVec_32_16 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_32_4`. -/
def ref_Vector_BitVec_32_4 (k : Bank_Vector_BitVec_32_4) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) where
  get r := r.bank_Vector_BitVec_32_4 k
  set v r := { r with bank_Vector_BitVec_32_4 := RegMap.set r.bank_Vector_BitVec_32_4 k v }
@[simp] theorem ref_Vector_BitVec_32_4_get (k : Bank_Vector_BitVec_32_4) (r : Regs) : (ref_Vector_BitVec_32_4 k).get r = r.bank_Vector_BitVec_32_4 k := rfl
@[simp] theorem ref_Vector_BitVec_32_4_set (k : Bank_Vector_BitVec_32_4) (v : (Vector (BitVec 32) 4)) (r : Regs) :
    (ref_Vector_BitVec_32_4 k).set v r = { r with bank_Vector_BitVec_32_4 := RegMap.set r.bank_Vector_BitVec_32_4 k v } := rfl
@[simp] theorem ref_Vector_BitVec_32_4_get_set_same (k : Bank_Vector_BitVec_32_4) (v : (Vector (BitVec 32) 4)) (r : Regs) :
    (ref_Vector_BitVec_32_4 k).get ((ref_Vector_BitVec_32_4 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_32_4_get_set_ne {k k' : Bank_Vector_BitVec_32_4} (v : (Vector (BitVec 32) 4)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_32_4 k').get ((ref_Vector_BitVec_32_4 k).set v r) = (ref_Vector_BitVec_32_4 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_64_32`. -/
def ref_Vector_BitVec_64_32 (k : Bank_Vector_BitVec_64_32) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) where
  get r := r.bank_Vector_BitVec_64_32 k
  set v r := { r with bank_Vector_BitVec_64_32 := RegMap.set r.bank_Vector_BitVec_64_32 k v }
@[simp] theorem ref_Vector_BitVec_64_32_get (k : Bank_Vector_BitVec_64_32) (r : Regs) : (ref_Vector_BitVec_64_32 k).get r = r.bank_Vector_BitVec_64_32 k := rfl
@[simp] theorem ref_Vector_BitVec_64_32_set (k : Bank_Vector_BitVec_64_32) (v : (Vector (BitVec 64) 32)) (r : Regs) :
    (ref_Vector_BitVec_64_32 k).set v r = { r with bank_Vector_BitVec_64_32 := RegMap.set r.bank_Vector_BitVec_64_32 k v } := rfl
@[simp] theorem ref_Vector_BitVec_64_32_get_set_same (k : Bank_Vector_BitVec_64_32) (v : (Vector (BitVec 64) 32)) (r : Regs) :
    (ref_Vector_BitVec_64_32 k).get ((ref_Vector_BitVec_64_32 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_64_32_get_set_ne {k k' : Bank_Vector_BitVec_64_32} (v : (Vector (BitVec 64) 32)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_64_32 k').get ((ref_Vector_BitVec_64_32 k).set v r) = (ref_Vector_BitVec_64_32 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_64`. -/
def ref_BitVec_64 (k : Bank_BitVec_64) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.bank_BitVec_64 k
  set v r := { r with bank_BitVec_64 := RegMap.set r.bank_BitVec_64 k v }
@[simp] theorem ref_BitVec_64_get (k : Bank_BitVec_64) (r : Regs) : (ref_BitVec_64 k).get r = r.bank_BitVec_64 k := rfl
@[simp] theorem ref_BitVec_64_set (k : Bank_BitVec_64) (v : (BitVec 64)) (r : Regs) :
    (ref_BitVec_64 k).set v r = { r with bank_BitVec_64 := RegMap.set r.bank_BitVec_64 k v } := rfl
@[simp] theorem ref_BitVec_64_get_set_same (k : Bank_BitVec_64) (v : (BitVec 64)) (r : Regs) :
    (ref_BitVec_64 k).get ((ref_BitVec_64 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_64_get_set_ne {k k' : Bank_BitVec_64} (v : (BitVec 64)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_64 k').get ((ref_BitVec_64 k).set v r) = (ref_BitVec_64 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_64_16`. -/
def ref_Vector_BitVec_64_16 (k : Bank_Vector_BitVec_64_16) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) where
  get r := r.bank_Vector_BitVec_64_16 k
  set v r := { r with bank_Vector_BitVec_64_16 := RegMap.set r.bank_Vector_BitVec_64_16 k v }
@[simp] theorem ref_Vector_BitVec_64_16_get (k : Bank_Vector_BitVec_64_16) (r : Regs) : (ref_Vector_BitVec_64_16 k).get r = r.bank_Vector_BitVec_64_16 k := rfl
@[simp] theorem ref_Vector_BitVec_64_16_set (k : Bank_Vector_BitVec_64_16) (v : (Vector (BitVec 64) 16)) (r : Regs) :
    (ref_Vector_BitVec_64_16 k).set v r = { r with bank_Vector_BitVec_64_16 := RegMap.set r.bank_Vector_BitVec_64_16 k v } := rfl
@[simp] theorem ref_Vector_BitVec_64_16_get_set_same (k : Bank_Vector_BitVec_64_16) (v : (Vector (BitVec 64) 16)) (r : Regs) :
    (ref_Vector_BitVec_64_16 k).get ((ref_Vector_BitVec_64_16 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_64_16_get_set_ne {k k' : Bank_Vector_BitVec_64_16} (v : (Vector (BitVec 64) 16)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_64_16 k').get ((ref_Vector_BitVec_64_16 k).set v r) = (ref_Vector_BitVec_64_16 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_64_4`. -/
def ref_Vector_BitVec_64_4 (k : Bank_Vector_BitVec_64_4) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) where
  get r := r.bank_Vector_BitVec_64_4 k
  set v r := { r with bank_Vector_BitVec_64_4 := RegMap.set r.bank_Vector_BitVec_64_4 k v }
@[simp] theorem ref_Vector_BitVec_64_4_get (k : Bank_Vector_BitVec_64_4) (r : Regs) : (ref_Vector_BitVec_64_4 k).get r = r.bank_Vector_BitVec_64_4 k := rfl
@[simp] theorem ref_Vector_BitVec_64_4_set (k : Bank_Vector_BitVec_64_4) (v : (Vector (BitVec 64) 4)) (r : Regs) :
    (ref_Vector_BitVec_64_4 k).set v r = { r with bank_Vector_BitVec_64_4 := RegMap.set r.bank_Vector_BitVec_64_4 k v } := rfl
@[simp] theorem ref_Vector_BitVec_64_4_get_set_same (k : Bank_Vector_BitVec_64_4) (v : (Vector (BitVec 64) 4)) (r : Regs) :
    (ref_Vector_BitVec_64_4 k).get ((ref_Vector_BitVec_64_4 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_64_4_get_set_ne {k k' : Bank_Vector_BitVec_64_4} (v : (Vector (BitVec 64) 4)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_64_4 k').get ((ref_Vector_BitVec_64_4 k).set v r) = (ref_Vector_BitVec_64_4 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_32_31`. -/
def ref_Vector_BitVec_32_31 (k : Bank_Vector_BitVec_32_31) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 31) where
  get r := r.bank_Vector_BitVec_32_31 k
  set v r := { r with bank_Vector_BitVec_32_31 := RegMap.set r.bank_Vector_BitVec_32_31 k v }
@[simp] theorem ref_Vector_BitVec_32_31_get (k : Bank_Vector_BitVec_32_31) (r : Regs) : (ref_Vector_BitVec_32_31 k).get r = r.bank_Vector_BitVec_32_31 k := rfl
@[simp] theorem ref_Vector_BitVec_32_31_set (k : Bank_Vector_BitVec_32_31) (v : (Vector (BitVec 32) 31)) (r : Regs) :
    (ref_Vector_BitVec_32_31 k).set v r = { r with bank_Vector_BitVec_32_31 := RegMap.set r.bank_Vector_BitVec_32_31 k v } := rfl
@[simp] theorem ref_Vector_BitVec_32_31_get_set_same (k : Bank_Vector_BitVec_32_31) (v : (Vector (BitVec 32) 31)) (r : Regs) :
    (ref_Vector_BitVec_32_31 k).get ((ref_Vector_BitVec_32_31 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_32_31_get_set_ne {k k' : Bank_Vector_BitVec_32_31} (v : (Vector (BitVec 32) 31)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_32_31 k').get ((ref_Vector_BitVec_32_31 k).set v r) = (ref_Vector_BitVec_32_31 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Bool`. -/
def ref_Bool (k : Bank_Bool) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool where
  get r := r.bank_Bool k
  set v r := { r with bank_Bool := RegMap.set r.bank_Bool k v }
@[simp] theorem ref_Bool_get (k : Bank_Bool) (r : Regs) : (ref_Bool k).get r = r.bank_Bool k := rfl
@[simp] theorem ref_Bool_set (k : Bank_Bool) (v : Bool) (r : Regs) :
    (ref_Bool k).set v r = { r with bank_Bool := RegMap.set r.bank_Bool k v } := rfl
@[simp] theorem ref_Bool_get_set_same (k : Bank_Bool) (v : Bool) (r : Regs) :
    (ref_Bool k).get ((ref_Bool k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Bool_get_set_ne {k k' : Bank_Bool} (v : Bool) (r : Regs) (h : k' ≠ k) :
    (ref_Bool k').get ((ref_Bool k).set v r) = (ref_Bool k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Int`. -/
def ref_Int (k : Bank_Int) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int where
  get r := r.bank_Int k
  set v r := { r with bank_Int := RegMap.set r.bank_Int k v }
@[simp] theorem ref_Int_get (k : Bank_Int) (r : Regs) : (ref_Int k).get r = r.bank_Int k := rfl
@[simp] theorem ref_Int_set (k : Bank_Int) (v : Int) (r : Regs) :
    (ref_Int k).set v r = { r with bank_Int := RegMap.set r.bank_Int k v } := rfl
@[simp] theorem ref_Int_get_set_same (k : Bank_Int) (v : Int) (r : Regs) :
    (ref_Int k).get ((ref_Int k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Int_get_set_ne {k k' : Bank_Int} (v : Int) (r : Regs) (h : k' ≠ k) :
    (ref_Int k').get ((ref_Int k).set v r) = (ref_Int k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_1`. -/
def ref_BitVec_1 (k : Bank_BitVec_1) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 1) where
  get r := r.bank_BitVec_1 k
  set v r := { r with bank_BitVec_1 := RegMap.set r.bank_BitVec_1 k v }
@[simp] theorem ref_BitVec_1_get (k : Bank_BitVec_1) (r : Regs) : (ref_BitVec_1 k).get r = r.bank_BitVec_1 k := rfl
@[simp] theorem ref_BitVec_1_set (k : Bank_BitVec_1) (v : (BitVec 1)) (r : Regs) :
    (ref_BitVec_1 k).set v r = { r with bank_BitVec_1 := RegMap.set r.bank_BitVec_1 k v } := rfl
@[simp] theorem ref_BitVec_1_get_set_same (k : Bank_BitVec_1) (v : (BitVec 1)) (r : Regs) :
    (ref_BitVec_1 k).get ((ref_BitVec_1 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_1_get_set_ne {k k' : Bank_BitVec_1} (v : (BitVec 1)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_1 k').get ((ref_BitVec_1 k).set v r) = (ref_BitVec_1 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_56`. -/
def ref_BitVec_56 (k : Bank_BitVec_56) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) where
  get r := r.bank_BitVec_56 k
  set v r := { r with bank_BitVec_56 := RegMap.set r.bank_BitVec_56 k v }
@[simp] theorem ref_BitVec_56_get (k : Bank_BitVec_56) (r : Regs) : (ref_BitVec_56 k).get r = r.bank_BitVec_56 k := rfl
@[simp] theorem ref_BitVec_56_set (k : Bank_BitVec_56) (v : (BitVec 56)) (r : Regs) :
    (ref_BitVec_56 k).set v r = { r with bank_BitVec_56 := RegMap.set r.bank_BitVec_56 k v } := rfl
@[simp] theorem ref_BitVec_56_get_set_same (k : Bank_BitVec_56) (v : (BitVec 56)) (r : Regs) :
    (ref_BitVec_56 k).get ((ref_BitVec_56 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_56_get_set_ne {k k' : Bank_BitVec_56} (v : (BitVec 56)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_56 k').get ((ref_BitVec_56 k).set v r) = (ref_BitVec_56 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_16`. -/
def ref_BitVec_16 (k : Bank_BitVec_16) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 16) where
  get r := r.bank_BitVec_16 k
  set v r := { r with bank_BitVec_16 := RegMap.set r.bank_BitVec_16 k v }
@[simp] theorem ref_BitVec_16_get (k : Bank_BitVec_16) (r : Regs) : (ref_BitVec_16 k).get r = r.bank_BitVec_16 k := rfl
@[simp] theorem ref_BitVec_16_set (k : Bank_BitVec_16) (v : (BitVec 16)) (r : Regs) :
    (ref_BitVec_16 k).set v r = { r with bank_BitVec_16 := RegMap.set r.bank_BitVec_16 k v } := rfl
@[simp] theorem ref_BitVec_16_get_set_same (k : Bank_BitVec_16) (v : (BitVec 16)) (r : Regs) :
    (ref_BitVec_16 k).get ((ref_BitVec_16 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_16_get_set_ne {k k' : Bank_BitVec_16} (v : (BitVec 16)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_16 k').get ((ref_BitVec_16 k).set v r) = (ref_BitVec_16 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_4`. -/
def ref_BitVec_4 (k : Bank_BitVec_4) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) where
  get r := r.bank_BitVec_4 k
  set v r := { r with bank_BitVec_4 := RegMap.set r.bank_BitVec_4 k v }
@[simp] theorem ref_BitVec_4_get (k : Bank_BitVec_4) (r : Regs) : (ref_BitVec_4 k).get r = r.bank_BitVec_4 k := rfl
@[simp] theorem ref_BitVec_4_set (k : Bank_BitVec_4) (v : (BitVec 4)) (r : Regs) :
    (ref_BitVec_4 k).set v r = { r with bank_BitVec_4 := RegMap.set r.bank_BitVec_4 k v } := rfl
@[simp] theorem ref_BitVec_4_get_set_same (k : Bank_BitVec_4) (v : (BitVec 4)) (r : Regs) :
    (ref_BitVec_4 k).get ((ref_BitVec_4 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_4_get_set_ne {k k' : Bank_BitVec_4} (v : (BitVec 4)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_4 k').get ((ref_BitVec_4 k).set v r) = (ref_BitVec_4 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_128`. -/
def ref_BitVec_128 (k : Bank_BitVec_128) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) where
  get r := r.bank_BitVec_128 k
  set v r := { r with bank_BitVec_128 := RegMap.set r.bank_BitVec_128 k v }
@[simp] theorem ref_BitVec_128_get (k : Bank_BitVec_128) (r : Regs) : (ref_BitVec_128 k).get r = r.bank_BitVec_128 k := rfl
@[simp] theorem ref_BitVec_128_set (k : Bank_BitVec_128) (v : (BitVec 128)) (r : Regs) :
    (ref_BitVec_128 k).set v r = { r with bank_BitVec_128 := RegMap.set r.bank_BitVec_128 k v } := rfl
@[simp] theorem ref_BitVec_128_get_set_same (k : Bank_BitVec_128) (v : (BitVec 128)) (r : Regs) :
    (ref_BitVec_128 k).get ((ref_BitVec_128 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_128_get_set_ne {k k' : Bank_BitVec_128} (v : (BitVec 128)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_128 k').get ((ref_BitVec_128 k).set v r) = (ref_BitVec_128 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_Bool_32`. -/
def ref_Vector_Bool_32 (k : Bank_Vector_Bool_32) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 32) where
  get r := r.bank_Vector_Bool_32 k
  set v r := { r with bank_Vector_Bool_32 := RegMap.set r.bank_Vector_Bool_32 k v }
@[simp] theorem ref_Vector_Bool_32_get (k : Bank_Vector_Bool_32) (r : Regs) : (ref_Vector_Bool_32 k).get r = r.bank_Vector_Bool_32 k := rfl
@[simp] theorem ref_Vector_Bool_32_set (k : Bank_Vector_Bool_32) (v : (Vector Bool 32)) (r : Regs) :
    (ref_Vector_Bool_32 k).set v r = { r with bank_Vector_Bool_32 := RegMap.set r.bank_Vector_Bool_32 k v } := rfl
@[simp] theorem ref_Vector_Bool_32_get_set_same (k : Bank_Vector_Bool_32) (v : (Vector Bool 32)) (r : Regs) :
    (ref_Vector_Bool_32 k).get ((ref_Vector_Bool_32 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_Bool_32_get_set_ne {k k' : Bank_Vector_Bool_32} (v : (Vector Bool 32)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_Bool_32 k').get ((ref_Vector_Bool_32 k).set v r) = (ref_Vector_Bool_32 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_64_64`. -/
def ref_Vector_BitVec_64_64 (k : Bank_Vector_BitVec_64_64) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) where
  get r := r.bank_Vector_BitVec_64_64 k
  set v r := { r with bank_Vector_BitVec_64_64 := RegMap.set r.bank_Vector_BitVec_64_64 k v }
@[simp] theorem ref_Vector_BitVec_64_64_get (k : Bank_Vector_BitVec_64_64) (r : Regs) : (ref_Vector_BitVec_64_64 k).get r = r.bank_Vector_BitVec_64_64 k := rfl
@[simp] theorem ref_Vector_BitVec_64_64_set (k : Bank_Vector_BitVec_64_64) (v : (Vector (BitVec 64) 64)) (r : Regs) :
    (ref_Vector_BitVec_64_64 k).set v r = { r with bank_Vector_BitVec_64_64 := RegMap.set r.bank_Vector_BitVec_64_64 k v } := rfl
@[simp] theorem ref_Vector_BitVec_64_64_get_set_same (k : Bank_Vector_BitVec_64_64) (v : (Vector (BitVec 64) 64)) (r : Regs) :
    (ref_Vector_BitVec_64_64 k).get ((ref_Vector_BitVec_64_64 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_64_64_get_set_ne {k k' : Bank_Vector_BitVec_64_64} (v : (Vector (BitVec 64) 64)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_64_64 k').get ((ref_Vector_BitVec_64_64 k).set v r) = (ref_Vector_BitVec_64_64 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Option_InterruptID`. -/
def ref_Option_InterruptID (k : Bank_Option_InterruptID) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Option InterruptID) where
  get r := r.bank_Option_InterruptID k
  set v r := { r with bank_Option_InterruptID := RegMap.set r.bank_Option_InterruptID k v }
@[simp] theorem ref_Option_InterruptID_get (k : Bank_Option_InterruptID) (r : Regs) : (ref_Option_InterruptID k).get r = r.bank_Option_InterruptID k := rfl
@[simp] theorem ref_Option_InterruptID_set (k : Bank_Option_InterruptID) (v : (Option InterruptID)) (r : Regs) :
    (ref_Option_InterruptID k).set v r = { r with bank_Option_InterruptID := RegMap.set r.bank_Option_InterruptID k v } := rfl
@[simp] theorem ref_Option_InterruptID_get_set_same (k : Bank_Option_InterruptID) (v : (Option InterruptID)) (r : Regs) :
    (ref_Option_InterruptID k).get ((ref_Option_InterruptID k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Option_InterruptID_get_set_ne {k k' : Bank_Option_InterruptID} (v : (Option InterruptID)) (r : Regs) (h : k' ≠ k) :
    (ref_Option_InterruptID k').get ((ref_Option_InterruptID k).set v r) = (ref_Option_InterruptID k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_8`. -/
def ref_BitVec_8 (k : Bank_BitVec_8) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 8) where
  get r := r.bank_BitVec_8 k
  set v r := { r with bank_BitVec_8 := RegMap.set r.bank_BitVec_8 k v }
@[simp] theorem ref_BitVec_8_get (k : Bank_BitVec_8) (r : Regs) : (ref_BitVec_8 k).get r = r.bank_BitVec_8 k := rfl
@[simp] theorem ref_BitVec_8_set (k : Bank_BitVec_8) (v : (BitVec 8)) (r : Regs) :
    (ref_BitVec_8 k).set v r = { r with bank_BitVec_8 := RegMap.set r.bank_BitVec_8 k v } := rfl
@[simp] theorem ref_BitVec_8_get_set_same (k : Bank_BitVec_8) (v : (BitVec 8)) (r : Regs) :
    (ref_BitVec_8 k).get ((ref_BitVec_8 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_8_get_set_ne {k k' : Bank_BitVec_8} (v : (BitVec 8)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_8 k').get ((ref_BitVec_8 k).set v r) = (ref_BitVec_8 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `BitVec_2`. -/
def ref_BitVec_2 (k : Bank_BitVec_2) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 2) where
  get r := r.bank_BitVec_2 k
  set v r := { r with bank_BitVec_2 := RegMap.set r.bank_BitVec_2 k v }
@[simp] theorem ref_BitVec_2_get (k : Bank_BitVec_2) (r : Regs) : (ref_BitVec_2 k).get r = r.bank_BitVec_2 k := rfl
@[simp] theorem ref_BitVec_2_set (k : Bank_BitVec_2) (v : (BitVec 2)) (r : Regs) :
    (ref_BitVec_2 k).set v r = { r with bank_BitVec_2 := RegMap.set r.bank_BitVec_2 k v } := rfl
@[simp] theorem ref_BitVec_2_get_set_same (k : Bank_BitVec_2) (v : (BitVec 2)) (r : Regs) :
    (ref_BitVec_2 k).get ((ref_BitVec_2 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_BitVec_2_get_set_ne {k k' : Bank_BitVec_2} (v : (BitVec 2)) (r : Regs) (h : k' ≠ k) :
    (ref_BitVec_2 k').get ((ref_BitVec_2 k).set v r) = (ref_BitVec_2 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Vector_BitVec_64_7`. -/
def ref_Vector_BitVec_64_7 (k : Bank_Vector_BitVec_64_7) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 7) where
  get r := r.bank_Vector_BitVec_64_7 k
  set v r := { r with bank_Vector_BitVec_64_7 := RegMap.set r.bank_Vector_BitVec_64_7 k v }
@[simp] theorem ref_Vector_BitVec_64_7_get (k : Bank_Vector_BitVec_64_7) (r : Regs) : (ref_Vector_BitVec_64_7 k).get r = r.bank_Vector_BitVec_64_7 k := rfl
@[simp] theorem ref_Vector_BitVec_64_7_set (k : Bank_Vector_BitVec_64_7) (v : (Vector (BitVec 64) 7)) (r : Regs) :
    (ref_Vector_BitVec_64_7 k).set v r = { r with bank_Vector_BitVec_64_7 := RegMap.set r.bank_Vector_BitVec_64_7 k v } := rfl
@[simp] theorem ref_Vector_BitVec_64_7_get_set_same (k : Bank_Vector_BitVec_64_7) (v : (Vector (BitVec 64) 7)) (r : Regs) :
    (ref_Vector_BitVec_64_7 k).get ((ref_Vector_BitVec_64_7 k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Vector_BitVec_64_7_get_set_ne {k k' : Bank_Vector_BitVec_64_7} (v : (Vector (BitVec 64) 7)) (r : Regs) (h : k' ≠ k) :
    (ref_Vector_BitVec_64_7 k').get ((ref_Vector_BitVec_64_7 k).set v r) = (ref_Vector_BitVec_64_7 k').get r := RegMap.set_ne _ _ h

/-- Typed reference to register `k` of bank `Signal`. -/
def ref_Signal (k : Bank_Signal) : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal where
  get r := r.bank_Signal k
  set v r := { r with bank_Signal := RegMap.set r.bank_Signal k v }
@[simp] theorem ref_Signal_get (k : Bank_Signal) (r : Regs) : (ref_Signal k).get r = r.bank_Signal k := rfl
@[simp] theorem ref_Signal_set (k : Bank_Signal) (v : Signal) (r : Regs) :
    (ref_Signal k).set v r = { r with bank_Signal := RegMap.set r.bank_Signal k v } := rfl
@[simp] theorem ref_Signal_get_set_same (k : Bank_Signal) (v : Signal) (r : Regs) :
    (ref_Signal k).get ((ref_Signal k).set v r) = v := RegMap.set_same _ _ _
@[simp] theorem ref_Signal_get_set_ne {k k' : Bank_Signal} (v : Signal) (r : Regs) (h : k' ≠ k) :
    (ref_Signal k').get ((ref_Signal k).set v r) = (ref_Signal k').get r := RegMap.set_ne _ _ h

end Regs

namespace Register

def __emulator_termination_opcode : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Option (BitVec 32)) where
  get r := r.__emulator_termination_opcode
  set v r := { r with __emulator_termination_opcode := v }
@[simp] theorem __emulator_termination_opcode_get (r : Regs) : __emulator_termination_opcode.get r = r.__emulator_termination_opcode := rfl
@[simp] theorem __emulator_termination_opcode_set (v : (Option (BitVec 32))) (r : Regs) : __emulator_termination_opcode.set v r = { r with __emulator_termination_opcode := v } := rfl
@[simp] theorem __emulator_termination_opcode_get_set_same (v : (Option (BitVec 32))) (r : Regs) : __emulator_termination_opcode.get (__emulator_termination_opcode.set v r) = v := rfl

def PMEVCNTSVR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 31) where
  get r := r.PMEVCNTSVR_EL1
  set v r := { r with PMEVCNTSVR_EL1 := v }
@[simp] theorem PMEVCNTSVR_EL1_get (r : Regs) : PMEVCNTSVR_EL1.get r = r.PMEVCNTSVR_EL1 := rfl
@[simp] theorem PMEVCNTSVR_EL1_set (v : (Vector (BitVec 64) 31)) (r : Regs) : PMEVCNTSVR_EL1.set v r = { r with PMEVCNTSVR_EL1 := v } := rfl
@[simp] theorem PMEVCNTSVR_EL1_get_set_same (v : (Vector (BitVec 64) 31)) (r : Regs) : PMEVCNTSVR_EL1.get (PMEVCNTSVR_EL1.set v r) = v := rfl

def SPESampleCounter : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Int 32) where
  get r := r.SPESampleCounter
  set v r := { r with SPESampleCounter := v }
@[simp] theorem SPESampleCounter_get (r : Regs) : SPESampleCounter.get r = r.SPESampleCounter := rfl
@[simp] theorem SPESampleCounter_set (v : (Vector Int 32)) (r : Regs) : SPESampleCounter.set v r = { r with SPESampleCounter := v } := rfl
@[simp] theorem SPESampleCounter_get_set_same (v : (Vector Int 32)) (r : Regs) : SPESampleCounter.get (SPESampleCounter.set v r) = v := rfl

def SPERecordData : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 8) 64) where
  get r := r.SPERecordData
  set v r := { r with SPERecordData := v }
@[simp] theorem SPERecordData_get (r : Regs) : SPERecordData.get r = r.SPERecordData := rfl
@[simp] theorem SPERecordData_set (v : (Vector (BitVec 8) 64)) (r : Regs) : SPERecordData.set v r = { r with SPERecordData := v } := rfl
@[simp] theorem SPERecordData_get_set_same (v : (Vector (BitVec 8) 64)) (r : Regs) : SPERecordData.get (SPERecordData.set v r) = v := rfl

def SP_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.SP_EL3
  set v r := { r with SP_EL3 := v }
@[simp] theorem SP_EL3_get (r : Regs) : SP_EL3.get r = r.SP_EL3 := rfl
@[simp] theorem SP_EL3_set (v : (BitVec 64)) (r : Regs) : SP_EL3.set v r = { r with SP_EL3 := v } := rfl
@[simp] theorem SP_EL3_get_set_same (v : (BitVec 64)) (r : Regs) : SP_EL3.get (SP_EL3.set v r) = v := rfl

def SP_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.SP_EL2
  set v r := { r with SP_EL2 := v }
@[simp] theorem SP_EL2_get (r : Regs) : SP_EL2.get r = r.SP_EL2 := rfl
@[simp] theorem SP_EL2_set (v : (BitVec 64)) (r : Regs) : SP_EL2.set v r = { r with SP_EL2 := v } := rfl
@[simp] theorem SP_EL2_get_set_same (v : (BitVec 64)) (r : Regs) : SP_EL2.get (SP_EL2.set v r) = v := rfl

def SP_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.SP_EL1
  set v r := { r with SP_EL1 := v }
@[simp] theorem SP_EL1_get (r : Regs) : SP_EL1.get r = r.SP_EL1 := rfl
@[simp] theorem SP_EL1_set (v : (BitVec 64)) (r : Regs) : SP_EL1.set v r = { r with SP_EL1 := v } := rfl
@[simp] theorem SP_EL1_get_set_same (v : (BitVec 64)) (r : Regs) : SP_EL1.get (SP_EL1.set v r) = v := rfl

def SP_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.SP_EL0
  set v r := { r with SP_EL0 := v }
@[simp] theorem SP_EL0_get (r : Regs) : SP_EL0.get r = r.SP_EL0 := rfl
@[simp] theorem SP_EL0_set (v : (BitVec 64)) (r : Regs) : SP_EL0.set v r = { r with SP_EL0 := v } := rfl
@[simp] theorem SP_EL0_get_set_same (v : (BitVec 64)) (r : Regs) : SP_EL0.get (SP_EL0.set v r) = v := rfl

def __mpam_vpmr_max : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 3) where
  get r := r.__mpam_vpmr_max
  set v r := { r with __mpam_vpmr_max := v }
@[simp] theorem __mpam_vpmr_max_get (r : Regs) : __mpam_vpmr_max.get r = r.__mpam_vpmr_max := rfl
@[simp] theorem __mpam_vpmr_max_set (v : (BitVec 3)) (r : Regs) : __mpam_vpmr_max.set v r = { r with __mpam_vpmr_max := v } := rfl
@[simp] theorem __mpam_vpmr_max_get_set_same (v : (BitVec 3)) (r : Regs) : __mpam_vpmr_max.get (__mpam_vpmr_max.set v r) = v := rfl

def __BranchTaken : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool where
  get r := r.__BranchTaken
  set v r := { r with __BranchTaken := v }
@[simp] theorem __BranchTaken_get (r : Regs) : __BranchTaken.get r = r.__BranchTaken := rfl
@[simp] theorem __BranchTaken_set (v : Bool) (r : Regs) : __BranchTaken.set v r = { r with __BranchTaken := v } := rfl
@[simp] theorem __BranchTaken_get_set_same (v : Bool) (r : Regs) : __BranchTaken.get (__BranchTaken.set v r) = v := rfl

def Branchtypetaken : Sail.ConcurrencyInterfaceV1.RegisterRef Regs BranchType where
  get r := r.Branchtypetaken
  set v r := { r with Branchtypetaken := v }
@[simp] theorem Branchtypetaken_get (r : Regs) : Branchtypetaken.get r = r.Branchtypetaken := rfl
@[simp] theorem Branchtypetaken_set (v : BranchType) (r : Regs) : Branchtypetaken.set v r = { r with Branchtypetaken := v } := rfl
@[simp] theorem Branchtypetaken_get_set_same (v : BranchType) (r : Regs) : Branchtypetaken.get (Branchtypetaken.set v r) = v := rfl

def __ThisInstrEnc : Sail.ConcurrencyInterfaceV1.RegisterRef Regs __InstrEnc where
  get r := r.__ThisInstrEnc
  set v r := { r with __ThisInstrEnc := v }
@[simp] theorem __ThisInstrEnc_get (r : Regs) : __ThisInstrEnc.get r = r.__ThisInstrEnc := rfl
@[simp] theorem __ThisInstrEnc_set (v : __InstrEnc) (r : Regs) : __ThisInstrEnc.set v r = { r with __ThisInstrEnc := v } := rfl
@[simp] theorem __ThisInstrEnc_get_set_same (v : __InstrEnc) (r : Regs) : __ThisInstrEnc.get (__ThisInstrEnc.set v r) = v := rfl

def __SPE_LFSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 24) where
  get r := r.__SPE_LFSR
  set v r := { r with __SPE_LFSR := v }
@[simp] theorem __SPE_LFSR_get (r : Regs) : __SPE_LFSR.get r = r.__SPE_LFSR := rfl
@[simp] theorem __SPE_LFSR_set (v : (BitVec 24)) (r : Regs) : __SPE_LFSR.set v r = { r with __SPE_LFSR := v } := rfl
@[simp] theorem __SPE_LFSR_get_set_same (v : (BitVec 24)) (r : Regs) : __SPE_LFSR.get (__SPE_LFSR.set v r) = v := rfl

def SPESampleOpType : Sail.ConcurrencyInterfaceV1.RegisterRef Regs OpType where
  get r := r.SPESampleOpType
  set v r := { r with SPESampleOpType := v }
@[simp] theorem SPESampleOpType_get (r : Regs) : SPESampleOpType.get r = r.SPESampleOpType := rfl
@[simp] theorem SPESampleOpType_set (v : OpType) (r : Regs) : SPESampleOpType.set v r = { r with SPESampleOpType := v } := rfl
@[simp] theorem SPESampleOpType_get_set_same (v : OpType) (r : Regs) : SPESampleOpType.get (SPESampleOpType.set v r) = v := rfl

def TSTATE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs TMState where
  get r := r.TSTATE
  set v r := { r with TSTATE := v }
@[simp] theorem TSTATE_get (r : Regs) : TSTATE.get r = r.TSTATE := rfl
@[simp] theorem TSTATE_set (v : TMState) (r : Regs) : TSTATE.set v r = { r with TSTATE := v } := rfl
@[simp] theorem TSTATE_get_set_same (v : TMState) (r : Regs) : TSTATE.get (TSTATE.set v r) = v := rfl

def FPSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.FPSR
  set v r := { r with FPSR := v }
@[simp] theorem FPSR_get (r : Regs) : FPSR.get r = r.FPSR := rfl
@[simp] theorem FPSR_set (v : (BitVec 64)) (r : Regs) : FPSR.set v r = { r with FPSR := v } := rfl
@[simp] theorem FPSR_get_set_same (v : (BitVec 64)) (r : Regs) : FPSR.get (FPSR.set v r) = v := rfl

def FPCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r.FPCR
  set v r := { r with FPCR := v }
@[simp] theorem FPCR_get (r : Regs) : FPCR.get r = r.FPCR := rfl
@[simp] theorem FPCR_set (v : (BitVec 64)) (r : Regs) : FPCR.set v r = { r with FPCR := v } := rfl
@[simp] theorem FPCR_get_set_same (v : (BitVec 64)) (r : Regs) : FPCR.get (FPCR.set v r) = v := rfl

def _ZT0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 512) where
  get r := r._ZT0
  set v r := { r with _ZT0 := v }
@[simp] theorem _ZT0_get (r : Regs) : _ZT0.get r = r._ZT0 := rfl
@[simp] theorem _ZT0_set (v : (BitVec 512)) (r : Regs) : _ZT0.set v r = { r with _ZT0 := v } := rfl
@[simp] theorem _ZT0_get_set_same (v : (BitVec 512)) (r : Regs) : _ZT0.get (_ZT0.set v r) = v := rfl

def _ZA : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 2048) 256) where
  get r := r._ZA
  set v r := { r with _ZA := v }
@[simp] theorem _ZA_get (r : Regs) : _ZA.get r = r._ZA := rfl
@[simp] theorem _ZA_set (v : (Vector (BitVec 2048) 256)) (r : Regs) : _ZA.set v r = { r with _ZA := v } := rfl
@[simp] theorem _ZA_get_set_same (v : (Vector (BitVec 2048) 256)) (r : Regs) : _ZA.get (_ZA.set v r) = v := rfl

def _FFR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 256) where
  get r := r._FFR
  set v r := { r with _FFR := v }
@[simp] theorem _FFR_get (r : Regs) : _FFR.get r = r._FFR := rfl
@[simp] theorem _FFR_set (v : (BitVec 256)) (r : Regs) : _FFR.set v r = { r with _FFR := v } := rfl
@[simp] theorem _FFR_get_set_same (v : (BitVec 256)) (r : Regs) : _FFR.get (_FFR.set v r) = v := rfl

def _P : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 256) 16) where
  get r := r._P
  set v r := { r with _P := v }
@[simp] theorem _P_get (r : Regs) : _P.get r = r._P := rfl
@[simp] theorem _P_set (v : (Vector (BitVec 256) 16)) (r : Regs) : _P.set v r = { r with _P := v } := rfl
@[simp] theorem _P_get_set_same (v : (Vector (BitVec 256) 16)) (r : Regs) : _P.get (_P.set v r) = v := rfl

def _Z : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 2048) 32) where
  get r := r._Z
  set v r := { r with _Z := v }
@[simp] theorem _Z_get (r : Regs) : _Z.get r = r._Z := rfl
@[simp] theorem _Z_set (v : (Vector (BitVec 2048) 32)) (r : Regs) : _Z.set v r = { r with _Z := v } := rfl
@[simp] theorem _Z_get_set_same (v : (Vector (BitVec 2048) 32)) (r : Regs) : _Z.get (_Z.set v r) = v := rfl

def BTypeCompatible : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool where
  get r := r.BTypeCompatible
  set v r := { r with BTypeCompatible := v }
@[simp] theorem BTypeCompatible_get (r : Regs) : BTypeCompatible.get r = r.BTypeCompatible := rfl
@[simp] theorem BTypeCompatible_set (v : Bool) (r : Regs) : BTypeCompatible.set v r = { r with BTypeCompatible := v } := rfl
@[simp] theorem BTypeCompatible_get_set_same (v : Bool) (r : Regs) : BTypeCompatible.get (BTypeCompatible.set v r) = v := rfl

def BTypeNext : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 2) where
  get r := r.BTypeNext
  set v r := { r with BTypeNext := v }
@[simp] theorem BTypeNext_get (r : Regs) : BTypeNext.get r = r.BTypeNext := rfl
@[simp] theorem BTypeNext_set (v : (BitVec 2)) (r : Regs) : BTypeNext.set v r = { r with BTypeNext := v } := rfl
@[simp] theorem BTypeNext_get_set_same (v : (BitVec 2)) (r : Regs) : BTypeNext.get (BTypeNext.set v r) = v := rfl

def RC : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 5) where
  get r := r.RC
  set v r := { r with RC := v }
@[simp] theorem RC_get (r : Regs) : RC.get r = r.RC := rfl
@[simp] theorem RC_set (v : (Vector (BitVec 64) 5)) (r : Regs) : RC.set v r = { r with RC := v } := rfl
@[simp] theorem RC_get_set_same (v : (Vector (BitVec 64) 5)) (r : Regs) : RC.get (RC.set v r) = v := rfl

def PhysicalCount : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 88) where
  get r := r.PhysicalCount
  set v r := { r with PhysicalCount := v }
@[simp] theorem PhysicalCount_get (r : Regs) : PhysicalCount.get r = r.PhysicalCount := rfl
@[simp] theorem PhysicalCount_set (v : (BitVec 88)) (r : Regs) : PhysicalCount.set v r = { r with PhysicalCount := v } := rfl
@[simp] theorem PhysicalCount_get_set_same (v : (BitVec 88)) (r : Regs) : PhysicalCount.get (PhysicalCount.set v r) = v := rfl

def _PC : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) where
  get r := r._PC
  set v r := { r with _PC := v }
@[simp] theorem _PC_get (r : Regs) : _PC.get r = r._PC := rfl
@[simp] theorem _PC_set (v : (BitVec 64)) (r : Regs) : _PC.set v r = { r with _PC := v } := rfl
@[simp] theorem _PC_get_set_same (v : (BitVec 64)) (r : Regs) : _PC.get (_PC.set v r) = v := rfl

def ShouldAdvanceSS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool where
  get r := r.ShouldAdvanceSS
  set v r := { r with ShouldAdvanceSS := v }
@[simp] theorem ShouldAdvanceSS_get (r : Regs) : ShouldAdvanceSS.get r = r.ShouldAdvanceSS := rfl
@[simp] theorem ShouldAdvanceSS_set (v : Bool) (r : Regs) : ShouldAdvanceSS.set v r = { r with ShouldAdvanceSS := v } := rfl
@[simp] theorem ShouldAdvanceSS_get_set_same (v : Bool) (r : Regs) : ShouldAdvanceSS.get (ShouldAdvanceSS.set v r) = v := rfl

def ShouldAdvanceIT : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool where
  get r := r.ShouldAdvanceIT
  set v r := { r with ShouldAdvanceIT := v }
@[simp] theorem ShouldAdvanceIT_get (r : Regs) : ShouldAdvanceIT.get r = r.ShouldAdvanceIT := rfl
@[simp] theorem ShouldAdvanceIT_set (v : Bool) (r : Regs) : ShouldAdvanceIT.set v r = { r with ShouldAdvanceIT := v } := rfl
@[simp] theorem ShouldAdvanceIT_get_set_same (v : Bool) (r : Regs) : ShouldAdvanceIT.get (ShouldAdvanceIT.set v r) = v := rfl

def PSTATE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs ProcState where
  get r := r.PSTATE
  set v r := { r with PSTATE := v }
@[simp] theorem PSTATE_get (r : Regs) : PSTATE.get r = r.PSTATE := rfl
@[simp] theorem PSTATE_set (v : ProcState) (r : Regs) : PSTATE.set v r = { r with PSTATE := v } := rfl
@[simp] theorem PSTATE_get_set_same (v : ProcState) (r : Regs) : PSTATE.get (PSTATE.set v r) = v := rfl

def PMULastThresholdValue : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 31) where
  get r := r.PMULastThresholdValue
  set v r := { r with PMULastThresholdValue := v }
@[simp] theorem PMULastThresholdValue_get (r : Regs) : PMULastThresholdValue.get r = r.PMULastThresholdValue := rfl
@[simp] theorem PMULastThresholdValue_set (v : (Vector Bool 31)) (r : Regs) : PMULastThresholdValue.set v r = { r with PMULastThresholdValue := v } := rfl
@[simp] theorem PMULastThresholdValue_get_set_same (v : (Vector Bool 31)) (r : Regs) : PMULastThresholdValue.get (PMULastThresholdValue.set v r) = v := rfl

def PMUEventAccumulator : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Int 31) where
  get r := r.PMUEventAccumulator
  set v r := { r with PMUEventAccumulator := v }
@[simp] theorem PMUEventAccumulator_get (r : Regs) : PMUEventAccumulator.get r = r.PMUEventAccumulator := rfl
@[simp] theorem PMUEventAccumulator_set (v : (Vector Int 31)) (r : Regs) : PMUEventAccumulator.set v r = { r with PMUEventAccumulator := v } := rfl
@[simp] theorem PMUEventAccumulator_get_set_same (v : (Vector Int 31)) (r : Regs) : PMUEventAccumulator.get (PMUEventAccumulator.set v r) = v := rfl

def VariantImplemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 16) where
  get r := r.VariantImplemented
  set v r := { r with VariantImplemented := v }
@[simp] theorem VariantImplemented_get (r : Regs) : VariantImplemented.get r = r.VariantImplemented := rfl
@[simp] theorem VariantImplemented_set (v : (Vector Bool 16)) (r : Regs) : VariantImplemented.set v r = { r with VariantImplemented := v } := rfl
@[simp] theorem VariantImplemented_get_set_same (v : (Vector Bool 16)) (r : Regs) : VariantImplemented.get (VariantImplemented.set v r) = v := rfl

def FeatureImpl : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 259) where
  get r := r.FeatureImpl
  set v r := { r with FeatureImpl := v }
@[simp] theorem FeatureImpl_get (r : Regs) : FeatureImpl.get r = r.FeatureImpl := rfl
@[simp] theorem FeatureImpl_set (v : (Vector Bool 259)) (r : Regs) : FeatureImpl.set v r = { r with FeatureImpl := v } := rfl
@[simp] theorem FeatureImpl_get_set_same (v : (Vector Bool 259)) (r : Regs) : FeatureImpl.get (FeatureImpl.set v r) = v := rfl

@[reducible] def R0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 0 (by decide)
@[reducible] def R1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 1 (by decide)
@[reducible] def R2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 2 (by decide)
@[reducible] def R3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 3 (by decide)
@[reducible] def R4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 4 (by decide)
@[reducible] def R5 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 5 (by decide)
@[reducible] def R6 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 6 (by decide)
@[reducible] def R7 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 7 (by decide)
@[reducible] def R8 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 8 (by decide)
@[reducible] def R9 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 9 (by decide)
@[reducible] def R10 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 10 (by decide)
@[reducible] def R11 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 11 (by decide)
@[reducible] def R12 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 12 (by decide)
@[reducible] def R13 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 13 (by decide)
@[reducible] def R14 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 14 (by decide)
@[reducible] def R15 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 15 (by decide)
@[reducible] def R16 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 16 (by decide)
@[reducible] def R17 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 17 (by decide)
@[reducible] def R18 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 18 (by decide)
@[reducible] def R19 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 19 (by decide)
@[reducible] def R20 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 20 (by decide)
@[reducible] def R21 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 21 (by decide)
@[reducible] def R22 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 22 (by decide)
@[reducible] def R23 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 23 (by decide)
@[reducible] def R24 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 24 (by decide)
@[reducible] def R25 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 25 (by decide)
@[reducible] def R26 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 26 (by decide)
@[reducible] def R27 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 27 (by decide)
@[reducible] def R28 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 28 (by decide)
@[reducible] def R29 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 29 (by decide)
@[reducible] def R30 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_gpr 30 (by decide)
@[reducible] def _HACTLR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HACTLR2
@[reducible] def _ERXSTATUS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXSTATUS
@[reducible] def _ERXMISC3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC3
@[reducible] def _ERXMISC7 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC7
@[reducible] def _ERXADDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXADDR2
@[reducible] def _ERXMISC4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC4
@[reducible] def _ERXMISC6 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC6
@[reducible] def _ERXCTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXCTLR
@[reducible] def _ERXMISC1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC1
@[reducible] def _ERXCTLR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXCTLR2
@[reducible] def _ERXMISC5 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC5
@[reducible] def _ERXMISC0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC0
@[reducible] def _ERXADDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXADDR
@[reducible] def _ERXFR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXFR
@[reducible] def _ERXMISC2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXMISC2
@[reducible] def _ERXFR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERXFR2
@[reducible] def _AMAIR1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMAIR1_NS
@[reducible] def AMAIR1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMAIR1_S
@[reducible] def _DBGDTRTXint : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDTRTXint
@[reducible] def _HTPIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HTPIDR
@[reducible] def _DBGDTRRXint : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDTRRXint
@[reducible] def _TPIDRPRW_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._TPIDRPRW_NS
@[reducible] def TPIDRPRW_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TPIDRPRW_S
@[reducible] def _HAIFSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HAIFSR
@[reducible] def _HAMAIR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HAMAIR1
@[reducible] def _ACTLR2_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ACTLR2_NS
@[reducible] def ACTLR2_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .ACTLR2_S
@[reducible] def _DBGOSECCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGOSECCR
@[reducible] def _PMINTENSET : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMINTENSET
@[reducible] def _CNTFRQ : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTFRQ
@[reducible] def _HADFSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HADFSR
@[reducible] def _AIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AIDR
@[reducible] def _HAMAIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HAMAIR0
@[reducible] def _AMAIR0_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMAIR0_NS
@[reducible] def AMAIR0_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMAIR0_S
@[reducible] def _DBGDTRRXext : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDTRRXext
@[reducible] def DBGOSLAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DBGOSLAR
@[reducible] def _ACTLR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ACTLR_NS
@[reducible] def ACTLR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .ACTLR_S
@[reducible] def _DBGDTRTXext : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDTRTXext
@[reducible] def _TPIDRURO_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._TPIDRURO_NS
@[reducible] def TPIDRURO_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TPIDRURO_S
@[reducible] def _REVIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._REVIDR
@[reducible] def _ADFSR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ADFSR_NS
@[reducible] def ADFSR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .ADFSR_S
@[reducible] def _TPIDRURW_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._TPIDRURW_NS
@[reducible] def TPIDRURW_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TPIDRURW_S
@[reducible] def TCMTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TCMTR
@[reducible] def _HACTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HACTLR
@[reducible] def _HACR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HACR
@[reducible] def _AIFSR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AIFSR_NS
@[reducible] def AIFSR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AIFSR_S
@[reducible] def _PMOVSSET : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMOVSSET
@[reducible] def DACR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DACR_S
@[reducible] def _DACR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DACR_NS
@[reducible] def _HMAIR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HMAIR1
@[reducible] def _HMAIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HMAIR0
@[reducible] def _MAIR1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MAIR1_S
@[reducible] def _MAIR1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MAIR1_NS
@[reducible] def _MAIR0_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MAIR0_S
@[reducible] def _MAIR0_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MAIR0_NS
@[reducible] def __CNTbase_frequency : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .__CNTbase_frequency
@[reducible] def GICD_TYPER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_TYPER
@[reducible] def EDDEVARCH : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDDEVARCH
@[reducible] def CTIDEVARCH : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIDEVARCH
@[reducible] def CNTFID0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTFID0
@[reducible] def CFG_MPIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CFG_MPIDR
@[reducible] def AMIIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMIIDR
@[reducible] def AMDEVARCH : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMDEVARCH
@[reducible] def _PMCEID3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCEID3
@[reducible] def _PMCEID2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCEID2
@[reducible] def _PMCEID1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCEID1
@[reducible] def _PMCEID0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCEID0
@[reducible] def _NMRR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._NMRR_NS
@[reducible] def NMRR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .NMRR_S
@[reducible] def _MVFR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MVFR1
@[reducible] def _MVFR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MVFR0
@[reducible] def _MIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MIDR
@[reducible] def _ID_PFR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_PFR1
@[reducible] def _ID_PFR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_PFR0
@[reducible] def _ID_MMFR4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_MMFR4
@[reducible] def _ID_MMFR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_MMFR3
@[reducible] def _ID_MMFR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_MMFR2
@[reducible] def _ID_MMFR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_MMFR1
@[reducible] def _ID_MMFR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_MMFR0
@[reducible] def _ID_ISAR6 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR6
@[reducible] def _ID_ISAR4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR4
@[reducible] def _ID_ISAR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR3
@[reducible] def _ID_ISAR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR2
@[reducible] def _ID_ISAR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR1
@[reducible] def _ID_DFR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_DFR0
@[reducible] def _CLIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CLIDR
@[reducible] def TLBTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TLBTR
@[reducible] def FPSID : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .FPSID
@[reducible] def DBGDEVID : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DBGDEVID
@[reducible] def _VTCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._VTCR
@[reducible] def _VPIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._VPIDR
@[reducible] def _VMPIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._VMPIDR
@[reducible] def _TTBCR2_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._TTBCR2_NS
@[reducible] def TTBCR2_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TTBCR2_S
@[reducible] def _TRFCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._TRFCR
@[reducible] def _RMR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._RMR
@[reducible] def _PRRR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PRRR_NS
@[reducible] def PRRR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PRRR_S
@[reducible] def _PMUSERENR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMUSERENR
@[reducible] def _PMSWINC : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMSWINC
@[reducible] def _PMSELR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMSELR
@[reducible] def _MVFR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MVFR2
@[reducible] def _MPIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._MPIDR
@[reducible] def _ISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ISR
@[reducible] def _ID_PFR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_PFR2
@[reducible] def _ID_MMFR5 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_MMFR5
@[reducible] def _ID_ISAR5 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR5
@[reducible] def _ID_ISAR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_ISAR0
@[reducible] def _ID_DFR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_DFR1
@[reducible] def _ID_AFR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ID_AFR0
@[reducible] def _ICV_RPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_RPR
@[reducible] def _ICV_PMR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_PMR
@[reducible] def _ICV_IGRPEN1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_IGRPEN1
@[reducible] def _ICV_IGRPEN0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_IGRPEN0
@[reducible] def _ICV_IAR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_IAR1
@[reducible] def _ICV_IAR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_IAR0
@[reducible] def _ICV_HPPIR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_HPPIR1
@[reducible] def _ICV_HPPIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_HPPIR0
@[reducible] def _ICV_EOIR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_EOIR1
@[reducible] def _ICV_EOIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_EOIR0
@[reducible] def _ICV_DIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_DIR
@[reducible] def _ICV_CTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_CTLR
@[reducible] def _ICV_BPR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_BPR1
@[reducible] def _ICV_BPR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICV_BPR0
@[reducible] def _ICH_VTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICH_VTR
@[reducible] def _ICH_VMCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICH_VMCR
@[reducible] def _ICH_MISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICH_MISR
@[reducible] def _ICH_HCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICH_HCR
@[reducible] def _ICH_ELRSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICH_ELRSR
@[reducible] def _ICH_EISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICH_EISR
@[reducible] def _ICC_SRE_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_SRE_S
@[reducible] def _ICC_SRE_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_SRE_NS
@[reducible] def _ICC_RPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_RPR
@[reducible] def _ICC_PMR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_PMR
@[reducible] def _ICC_IGRPEN1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_IGRPEN1_S
@[reducible] def _ICC_IGRPEN1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_IGRPEN1_NS
@[reducible] def _ICC_IGRPEN0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_IGRPEN0
@[reducible] def _ICC_IAR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_IAR1
@[reducible] def _ICC_IAR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_IAR0
@[reducible] def _ICC_HSRE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_HSRE
@[reducible] def _ICC_HPPIR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_HPPIR1
@[reducible] def _ICC_HPPIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_HPPIR0
@[reducible] def _ICC_EOIR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_EOIR1
@[reducible] def _ICC_EOIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_EOIR0
@[reducible] def _ICC_DIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_DIR
@[reducible] def _ICC_CTLR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_CTLR_S
@[reducible] def _ICC_CTLR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_CTLR_NS
@[reducible] def _ICC_BPR1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_BPR1_S
@[reducible] def _ICC_BPR1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_BPR1_NS
@[reducible] def _ICC_BPR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ICC_BPR0
@[reducible] def _HTRFCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HTRFCR
@[reducible] def _HTCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HTCR
@[reducible] def _HSTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HSTR
@[reducible] def _HRMR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HRMR
@[reducible] def _ERRSELR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERRSELR
@[reducible] def _ERRIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ERRIDR
@[reducible] def _DBGVCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGVCR
@[reducible] def _DBGDCCINT : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDCCINT
@[reducible] def _DBGCLAIMSET : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGCLAIMSET
@[reducible] def _DBGCLAIMCLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGCLAIMCLR
@[reducible] def _DBGAUTHSTATUS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGAUTHSTATUS
@[reducible] def _CTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CTR
@[reducible] def _CSSELR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CSSELR_NS
@[reducible] def CSSELR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CSSELR_S
@[reducible] def _CNTV_CTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTV_CTL
@[reducible] def _CNTHV_CTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTHV_CTL
@[reducible] def _CNTHVS_CTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTHVS_CTL
@[reducible] def _CNTHPS_CTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTHPS_CTL
@[reducible] def _CNTHCTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTHCTL
@[reducible] def _CCSIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CCSIDR
@[reducible] def _CCSIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CCSIDR2
@[reducible] def _AMUSERENR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMUSERENR
@[reducible] def _AMCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCR
@[reducible] def _AMCNTENSET1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCNTENSET1
@[reducible] def _AMCNTENSET0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCNTENSET0
@[reducible] def _AMCNTENCLR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCNTENCLR1
@[reducible] def _AMCNTENCLR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCNTENCLR0
@[reducible] def _AMCGCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCGCR
@[reducible] def _AMCFGR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._AMCFGR
@[reducible] def PMVIDSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMVIDSR
@[reducible] def PMPIDR4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMPIDR4
@[reducible] def PMPIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMPIDR3
@[reducible] def PMPIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMPIDR2
@[reducible] def PMPIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMPIDR1
@[reducible] def PMPIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMPIDR0
@[reducible] def PMMIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMMIR
@[reducible] def PMLSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMLSR
@[reducible] def PMLAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMLAR
@[reducible] def PMITCTRL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMITCTRL
@[reducible] def PMDEVTYPE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMDEVTYPE
@[reducible] def PMDEVID : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMDEVID
@[reducible] def PMCIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMCIDR3
@[reducible] def PMCIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMCIDR2
@[reducible] def PMCIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMCIDR1
@[reducible] def PMCIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMCIDR0
@[reducible] def PMCGCR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMCGCR0
@[reducible] def PMAUTHSTATUS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .PMAUTHSTATUS
@[reducible] def JOSCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .JOSCR
@[reducible] def JMCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .JMCR
@[reducible] def JIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .JIDR
@[reducible] def ICC_MSRE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .ICC_MSRE
@[reducible] def ICC_MGRPEN1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .ICC_MGRPEN1
@[reducible] def ICC_MCTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .ICC_MCTLR
@[reducible] def GITS_STATUSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GITS_STATUSR
@[reducible] def GITS_PARTIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GITS_PARTIDR
@[reducible] def GITS_MPIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GITS_MPIDR
@[reducible] def GITS_MPAMIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GITS_MPAMIDR
@[reducible] def GITS_IIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GITS_IIDR
@[reducible] def GITS_CTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GITS_CTLR
@[reducible] def GICV_STATUSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_STATUSR
@[reducible] def GICV_RPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_RPR
@[reducible] def GICV_PMR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_PMR
@[reducible] def GICV_IAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_IAR
@[reducible] def GICV_HPPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_HPPIR
@[reducible] def GICV_EOIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_EOIR
@[reducible] def GICV_DIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_DIR
@[reducible] def GICV_CTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_CTLR
@[reducible] def GICV_BPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_BPR
@[reducible] def GICV_AIAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_AIAR
@[reducible] def GICV_AHPPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_AHPPIR
@[reducible] def GICV_AEOIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_AEOIR
@[reducible] def GICV_ABPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICV_ABPR
@[reducible] def GICR_WAKER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_WAKER
@[reducible] def GICR_VSGIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_VSGIR
@[reducible] def GICR_VSGIPENDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_VSGIPENDR
@[reducible] def GICR_SYNCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_SYNCR
@[reducible] def GICR_STATUSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_STATUSR
@[reducible] def GICR_PARTIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_PARTIDR
@[reducible] def GICR_MPAMIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_MPAMIDR
@[reducible] def GICR_ISENABLER0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_ISENABLER0
@[reducible] def GICR_INMIR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_INMIR0
@[reducible] def GICR_IIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_IIDR
@[reducible] def GICR_CTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICR_CTLR
@[reducible] def GICM_TYPER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICM_TYPER
@[reducible] def GICM_SETSPI_SR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICM_SETSPI_SR
@[reducible] def GICM_SETSPI_NSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICM_SETSPI_NSR
@[reducible] def GICM_IIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICM_IIDR
@[reducible] def GICM_CLRSPI_SR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICM_CLRSPI_SR
@[reducible] def GICM_CLRSPI_NSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICM_CLRSPI_NSR
@[reducible] def GICH_VTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICH_VTR
@[reducible] def GICH_VMCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICH_VMCR
@[reducible] def GICH_MISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICH_MISR
@[reducible] def GICH_HCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICH_HCR
@[reducible] def GICH_ELRSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICH_ELRSR
@[reducible] def GICH_EISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICH_EISR
@[reducible] def GICD_TYPER2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_TYPER2
@[reducible] def GICD_STATUSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_STATUSR
@[reducible] def GICD_SGIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_SGIR
@[reducible] def GICD_SETSPI_SR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_SETSPI_SR
@[reducible] def GICD_SETSPI_NSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_SETSPI_NSR
@[reducible] def GICD_IIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_IIDR
@[reducible] def GICD_CTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_CTLR
@[reducible] def GICD_CLRSPI_SR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_CLRSPI_SR
@[reducible] def GICD_CLRSPI_NSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICD_CLRSPI_NSR
@[reducible] def GICC_STATUSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_STATUSR
@[reducible] def GICC_RPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_RPR
@[reducible] def GICC_PMR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_PMR
@[reducible] def GICC_IAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_IAR
@[reducible] def GICC_HPPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_HPPIR
@[reducible] def GICC_EOIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_EOIR
@[reducible] def GICC_DIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_DIR
@[reducible] def GICC_BPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_BPR
@[reducible] def GICC_AIAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_AIAR
@[reducible] def GICC_AHPPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_AHPPIR
@[reducible] def GICC_AEOIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_AEOIR
@[reducible] def GICC_ABPR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_ABPR
@[reducible] def FCSEIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .FCSEIDR
@[reducible] def EDVIDSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDVIDSR
@[reducible] def EDRCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDRCR
@[reducible] def EDPRSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPRSR
@[reducible] def EDPRCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPRCR
@[reducible] def EDPIDR4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPIDR4
@[reducible] def EDPIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPIDR3
@[reducible] def EDPIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPIDR2
@[reducible] def EDPIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPIDR1
@[reducible] def EDPIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDPIDR0
@[reducible] def EDLSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDLSR
@[reducible] def EDLAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDLAR
@[reducible] def EDITCTRL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDITCTRL
@[reducible] def EDDEVTYPE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDDEVTYPE
@[reducible] def EDDEVID2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDDEVID2
@[reducible] def EDDEVID1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDDEVID1
@[reducible] def EDDEVID : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDDEVID
@[reducible] def EDCIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDCIDR3
@[reducible] def EDCIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDCIDR2
@[reducible] def EDCIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDCIDR1
@[reducible] def EDCIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDCIDR0
@[reducible] def DBGWFAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DBGWFAR
@[reducible] def DBGDIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DBGDIDR
@[reducible] def DBGDEVID2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DBGDEVID2
@[reducible] def DBGDEVID1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DBGDEVID1
@[reducible] def CTIPIDR4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIPIDR4
@[reducible] def CTIPIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIPIDR3
@[reducible] def CTIPIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIPIDR2
@[reducible] def CTIPIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIPIDR1
@[reducible] def CTIPIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIPIDR0
@[reducible] def CTILSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTILSR
@[reducible] def CTILAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTILAR
@[reducible] def CTIITCTRL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIITCTRL
@[reducible] def CTIDEVTYPE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIDEVTYPE
@[reducible] def CTIDEVID2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIDEVID2
@[reducible] def CTIDEVID1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIDEVID1
@[reducible] def CTIDEVID : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIDEVID
@[reducible] def CTIDEVCTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIDEVCTL
@[reducible] def CTICONTROL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTICONTROL
@[reducible] def CTICIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTICIDR3
@[reducible] def CTICIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTICIDR2
@[reducible] def CTICIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTICIDR1
@[reducible] def CTICIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTICIDR0
@[reducible] def CTIAUTHSTATUS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CTIAUTHSTATUS
@[reducible] def CNTSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTSR
@[reducible] def CNTNSAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTNSAR
@[reducible] def CNTID : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTID
@[reducible] def CNTEL0ACR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTEL0ACR
@[reducible] def AMPIDR4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMPIDR4
@[reducible] def AMPIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMPIDR3
@[reducible] def AMPIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMPIDR2
@[reducible] def AMPIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMPIDR1
@[reducible] def AMPIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMPIDR0
@[reducible] def AMDEVTYPE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMDEVTYPE
@[reducible] def AMCIDR3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMCIDR3
@[reducible] def AMCIDR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMCIDR2
@[reducible] def AMCIDR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMCIDR1
@[reducible] def AMCIDR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .AMCIDR0
@[reducible] def _VDISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._VDISR
@[reducible] def _VDFSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._VDFSR
@[reducible] def _DISR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DISR
@[reducible] def _EDSCR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._EDSCR2
@[reducible] def _CNTKCTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTKCTL
@[reducible] def GICC_CTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .GICC_CTLR
@[reducible] def CNTSCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTSCR
@[reducible] def CNTCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTCR
@[reducible] def CNTP_CTL_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CNTP_CTL_S
@[reducible] def _CNTP_CTL_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTP_CTL_NS
@[reducible] def _CNTHP_CTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CNTHP_CTL
@[reducible] def _FPEXC : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._FPEXC
@[reducible] def _IFAR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._IFAR_S
@[reducible] def _IFAR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._IFAR_NS
@[reducible] def _HCR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HCR2
@[reducible] def _DBGDSCRext : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDSCRext
@[reducible] def _DBGDSCRint : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGDSCRint
@[reducible] def IFSR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .IFSR_S
@[reducible] def _IFSR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._IFSR_NS
@[reducible] def DFSR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .DFSR_S
@[reducible] def _DFSR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DFSR_NS
@[reducible] def _DFAR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DFAR_S
@[reducible] def _DFAR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DFAR_NS
@[reducible] def MVBAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .MVBAR
@[reducible] def _HVBAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HVBAR
@[reducible] def _ELR_hyp : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ELR_hyp
@[reducible] def _HSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HSR
@[reducible] def _HPFAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HPFAR
@[reducible] def _HIFAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HIFAR
@[reducible] def _HDFAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HDFAR
@[reducible] def CONTEXTIDR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .CONTEXTIDR_S
@[reducible] def _CONTEXTIDR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CONTEXTIDR_NS
@[reducible] def TTBCR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .TTBCR_S
@[reducible] def _TTBCR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._TTBCR_NS
@[reducible] def VBAR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .VBAR_S
@[reducible] def _VBAR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._VBAR_NS
@[reducible] def EDESR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDESR
@[reducible] def _EDECCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._EDECCR
@[reducible] def _SPSR_svc : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._SPSR_svc
@[reducible] def SPSR_mon : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SPSR_mon
@[reducible] def _SPSR_hyp : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._SPSR_hyp
@[reducible] def SCTLR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SCTLR_S
@[reducible] def _SCTLR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._SCTLR_NS
@[reducible] def _HSCTLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HSCTLR
@[reducible] def _HCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HCR
@[reducible] def _DBGOSLSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGOSLSR
@[reducible] def _DBGPRCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGPRCR
@[reducible] def _DBGOSDLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DBGOSDLR
@[reducible] def NSACR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .NSACR
@[reducible] def _HCPTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HCPTR
@[reducible] def _CPACR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._CPACR
@[reducible] def _DSPSR2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DSPSR2
@[reducible] def _DSPSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DSPSR
@[reducible] def _DLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DLR
@[reducible] def EDECR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .EDECR
@[reducible] def _SDER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._SDER
@[reducible] def SDCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SDCR
@[reducible] def _PMCNTENSET : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCNTENSET
@[reducible] def _PMCCFILTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCCFILTR
@[reducible] def _PMOVSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMOVSR
@[reducible] def _PMINTENCLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMINTENCLR
@[reducible] def _PMCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCR
@[reducible] def _PMCNTENCLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._PMCNTENCLR
@[reducible] def _EDSCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._EDSCR
@[reducible] def _HDCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._HDCR
@[reducible] def RVBAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .RVBAR
@[reducible] def _FPSCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._FPSCR
@[reducible] def SCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SCR
@[reducible] def LR_mon : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .LR_mon
@[reducible] def SP_mon : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SP_mon
@[reducible] def __ThisInstr : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .__ThisInstr
@[reducible] def SPESampleContextEL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SPESampleContextEL2
@[reducible] def SPESampleContextEL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .SPESampleContextEL1
@[reducible] def _DormantCtlReg : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._DormantCtlReg
@[reducible] def _ConfigReg : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 ._ConfigReg
@[reducible] def __trcclaim_tags : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32) := Regs.ref_BitVec_32 .__trcclaim_tags
@[reducible] def _AMEVTYPER1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._AMEVTYPER1
@[reducible] def _ICH_LRC : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._ICH_LRC
@[reducible] def _ICH_LR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._ICH_LR
@[reducible] def _DBGWVR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._DBGWVR
@[reducible] def _DBGWCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._DBGWCR
@[reducible] def _DBGBXVR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._DBGBXVR
@[reducible] def _DBGBVR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._DBGBVR
@[reducible] def _DBGBCR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16) := Regs.ref_Vector_BitVec_32_16 ._DBGBCR
@[reducible] def _AMEVTYPER0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._AMEVTYPER0
@[reducible] def _ICC_AP0R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICC_AP0R
@[reducible] def _ICH_AP0R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICH_AP0R
@[reducible] def _ICH_AP1R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICH_AP1R
@[reducible] def _ICC_AP1R_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICC_AP1R_NS
@[reducible] def _ICC_AP1R_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICC_AP1R_S
@[reducible] def _ICV_AP1R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICV_AP1R
@[reducible] def _ICV_AP0R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4) := Regs.ref_Vector_BitVec_32_4 ._ICV_AP0R
@[reducible] def BRBSRC_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 .BRBSRC_EL1
@[reducible] def BRBTGT_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 .BRBTGT_EL1
@[reducible] def BRBINF_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 .BRBINF_EL1
@[reducible] def PMEVCNTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 .PMEVCNTR_EL0
@[reducible] def SPESampleAddress : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 .SPESampleAddress
@[reducible] def PMEVTYPER_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 .PMEVTYPER_EL0
@[reducible] def _Dclone : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32) := Regs.ref_Vector_BitVec_64_32 ._Dclone
@[reducible] def ERXPFGCTL_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXPFGCTL_EL1
@[reducible] def ERXMISC2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXMISC2_EL1
@[reducible] def ERXMISC3_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXMISC3_EL1
@[reducible] def ERXGSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXGSR_EL1
@[reducible] def ERXFR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXFR_EL1
@[reducible] def ERXSTATUS_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXSTATUS_EL1
@[reducible] def ERXCTLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXCTLR_EL1
@[reducible] def ERXMISC1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXMISC1_EL1
@[reducible] def ERXPFGF_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXPFGF_EL1
@[reducible] def ERXPFGCDN_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXPFGCDN_EL1
@[reducible] def ERXMISC0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXMISC0_EL1
@[reducible] def ERXADDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERXADDR_EL1
@[reducible] def _CNTV_CVAL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._CNTV_CVAL
@[reducible] def _CNTVOFF : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._CNTVOFF
@[reducible] def SPMACCESSR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPMACCESSR_EL3
@[reducible] def AMAIR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMAIR2_EL1
@[reducible] def AFSR0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AFSR0_EL2
@[reducible] def AFSR1_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AFSR1_EL3
@[reducible] def AMAIR2_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMAIR2_EL3
@[reducible] def HACR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HACR_EL2
@[reducible] def RNDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RNDR
@[reducible] def SMPRIMAP_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SMPRIMAP_EL2
@[reducible] def RNDRRS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RNDRRS
@[reducible] def TPIDR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TPIDR_EL0
@[reducible] def SCXTNUM_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCXTNUM_EL3
@[reducible] def TPIDR2_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TPIDR2_EL0
@[reducible] def SCXTNUM_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCXTNUM_EL0
@[reducible] def AMAIR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMAIR_EL1
@[reducible] def TPIDRRO_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TPIDRRO_EL0
@[reducible] def SCXTNUM_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCXTNUM_EL1
@[reducible] def AMAIR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMAIR_EL3
@[reducible] def AMAIR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMAIR_EL2
@[reducible] def ACTLR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ACTLR_EL3
@[reducible] def TPIDR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TPIDR_EL3
@[reducible] def PMIAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMIAR_EL1
@[reducible] def SCXTNUM_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCXTNUM_EL2
@[reducible] def PMICNTSVR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMICNTSVR_EL1
@[reducible] def SPMACCESSR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPMACCESSR_EL2
@[reducible] def AFSR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AFSR0_EL1
@[reducible] def AFSR1_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AFSR1_EL2
@[reducible] def AFSR0_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AFSR0_EL3
@[reducible] def AMAIR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMAIR2_EL2
@[reducible] def PMCCNTSVR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCCNTSVR_EL1
@[reducible] def AFSR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AFSR1_EL1
@[reducible] def ACTLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ACTLR_EL1
@[reducible] def TPIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TPIDR_EL1
@[reducible] def SPMACCESSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPMACCESSR_EL1
@[reducible] def ACTLR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ACTLR_EL2
@[reducible] def TPIDR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TPIDR_EL2
@[reducible] def REVIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .REVIDR_EL1
@[reducible] def AIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AIDR_EL1
@[reducible] def _PMCCNTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._PMCCNTR
@[reducible] def STACK_LIMIT : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .STACK_LIMIT
@[reducible] def STACK_BASE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .STACK_BASE
@[reducible] def HEAP_LIMIT : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HEAP_LIMIT
@[reducible] def HEAP_BASE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HEAP_BASE
@[reducible] def _DBGDTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._DBGDTR_EL0
@[reducible] def BRBTGTINJ_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBTGTINJ_EL1
@[reducible] def BRBSRCINJ_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBSRCINJ_EL1
@[reducible] def PMSDSFR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSDSFR_EL1
@[reducible] def PMBPTR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMBPTR_EL1
@[reducible] def PMCCNTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCCNTR_EL0
@[reducible] def ID_AA64PFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64PFR0_EL1
@[reducible] def ID_AA64MMFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64MMFR1_EL1
@[reducible] def ID_AA64ISAR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64ISAR1_EL1
@[reducible] def ID_AA64DFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64DFR1_EL1
@[reducible] def ID_AA64DFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64DFR0_EL1
@[reducible] def SPMSELR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPMSELR_EL0
@[reducible] def SMPRI_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SMPRI_EL1
@[reducible] def SMIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SMIDR_EL1
@[reducible] def PMZR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMZR_EL0
@[reducible] def PMXEVCNTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMXEVCNTR_EL0
@[reducible] def PMUACR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMUACR_EL1
@[reducible] def PMSSCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSSCR_EL1
@[reducible] def PMSNEVFR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSNEVFR_EL1
@[reducible] def PMSLATFR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSLATFR_EL1
@[reducible] def PMSIRR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSIRR_EL1
@[reducible] def PMSICR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSICR_EL1
@[reducible] def PMSFCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSFCR_EL1
@[reducible] def PMSEVFR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSEVFR_EL1
@[reducible] def PMMIR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMMIR_EL1
@[reducible] def PMECR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMECR_EL1
@[reducible] def PMBIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMBIDR_EL1
@[reducible] def OSLAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .OSLAR_EL1
@[reducible] def OSDTRTX_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .OSDTRTX_EL1
@[reducible] def OSDTRRX_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .OSDTRRX_EL1
@[reducible] def MECIDR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MECIDR_EL2
@[reducible] def MDSELR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDSELR_EL1
@[reducible] def LORSA_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .LORSA_EL1
@[reducible] def LORN_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .LORN_EL1
@[reducible] def LORID_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .LORID_EL1
@[reducible] def LOREA_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .LOREA_EL1
@[reducible] def LORC_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .LORC_EL1
@[reducible] def ID_AA64ZFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64ZFR0_EL1
@[reducible] def ID_AA64SMFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64SMFR0_EL1
@[reducible] def ID_AA64PFR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64PFR2_EL1
@[reducible] def ID_AA64PFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64PFR1_EL1
@[reducible] def ID_AA64MMFR4_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64MMFR4_EL1
@[reducible] def ID_AA64MMFR3_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64MMFR3_EL1
@[reducible] def ID_AA64MMFR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64MMFR2_EL1
@[reducible] def ID_AA64MMFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64MMFR0_EL1
@[reducible] def ID_AA64ISAR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64ISAR2_EL1
@[reducible] def ID_AA64ISAR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64ISAR0_EL1
@[reducible] def ID_AA64AFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64AFR1_EL1
@[reducible] def ID_AA64AFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AA64AFR0_EL1
@[reducible] def ICV_NMIAR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_NMIAR1_EL1
@[reducible] def ICC_SRE_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_SRE_EL3
@[reducible] def ICC_NMIAR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_NMIAR1_EL1
@[reducible] def ICC_IGRPEN1_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_IGRPEN1_EL3
@[reducible] def ICC_CTLR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_CTLR_EL3
@[reducible] def HFGWTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HFGWTR_EL2
@[reducible] def HFGWTR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HFGWTR2_EL2
@[reducible] def HFGRTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HFGRTR_EL2
@[reducible] def HFGRTR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HFGRTR2_EL2
@[reducible] def HFGITR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HFGITR2_EL2
@[reducible] def HDFGWTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HDFGWTR_EL2
@[reducible] def HDFGWTR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HDFGWTR2_EL2
@[reducible] def HDFGRTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HDFGRTR_EL2
@[reducible] def HDFGRTR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HDFGRTR2_EL2
@[reducible] def HAFGRTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HAFGRTR_EL2
@[reducible] def GMID_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GMID_EL1
@[reducible] def DCZID_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DCZID_EL0
@[reducible] def DBGDTRTX_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGDTRTX_EL0
@[reducible] def DBGDTRRX_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGDTRRX_EL0
@[reducible] def DACR32_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DACR32_EL2
@[reducible] def CNTV_TVAL_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTV_TVAL_EL0
@[reducible] def CNTP_TVAL_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTP_TVAL_EL0
@[reducible] def CNTPS_TVAL_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTPS_TVAL_EL1
@[reducible] def CNTHV_TVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHV_TVAL_EL2
@[reducible] def CNTHVS_TVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHVS_TVAL_EL2
@[reducible] def CNTHP_TVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHP_TVAL_EL2
@[reducible] def CNTHPS_TVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHPS_TVAL_EL2
@[reducible] def CNTFRQ_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTFRQ_EL0
@[reducible] def BRBINFINJ_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBINFINJ_EL1
@[reducible] def AMCG1IDR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCG1IDR_EL0
@[reducible] def ACCDATA_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ACCDATA_EL1
@[reducible] def PMCEID1_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCEID1_EL0
@[reducible] def PMCEID0_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCEID0_EL0
@[reducible] def MVFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MVFR1_EL1
@[reducible] def MVFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MVFR0_EL1
@[reducible] def MIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MIDR_EL1
@[reducible] def ID_PFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_PFR1_EL1
@[reducible] def ID_PFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_PFR0_EL1
@[reducible] def ID_MMFR4_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_MMFR4_EL1
@[reducible] def ID_MMFR3_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_MMFR3_EL1
@[reducible] def ID_MMFR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_MMFR2_EL1
@[reducible] def ID_MMFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_MMFR1_EL1
@[reducible] def ID_MMFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_MMFR0_EL1
@[reducible] def ID_ISAR6_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR6_EL1
@[reducible] def ID_ISAR4_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR4_EL1
@[reducible] def ID_ISAR3_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR3_EL1
@[reducible] def ID_ISAR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR2_EL1
@[reducible] def ID_ISAR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR1_EL1
@[reducible] def ID_DFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_DFR0_EL1
@[reducible] def VPIDR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VPIDR_EL2
@[reducible] def VMPIDR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VMPIDR_EL2
@[reducible] def TRFCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TRFCR_EL1
@[reducible] def RMR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RMR_EL3
@[reducible] def RMR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RMR_EL1
@[reducible] def PMUSERENR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMUSERENR_EL0
@[reducible] def PMSWINC_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSWINC_EL0
@[reducible] def PMSELR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSELR_EL0
@[reducible] def _PMOVS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._PMOVS
@[reducible] def _PMINTEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._PMINTEN
@[reducible] def PMINTENSET_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMINTENSET_EL1
@[reducible] def _PMCNTEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._PMCNTEN
@[reducible] def PAR_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PAR_S
@[reducible] def PAR_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PAR_NS
@[reducible] def MVFR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MVFR2_EL1
@[reducible] def MPIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPIDR_EL1
@[reducible] def ISR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ISR_EL1
@[reducible] def ID_PFR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_PFR2_EL1
@[reducible] def ID_MMFR5_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_MMFR5_EL1
@[reducible] def ID_ISAR5_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR5_EL1
@[reducible] def ID_ISAR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_ISAR0_EL1
@[reducible] def ID_DFR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_DFR1_EL1
@[reducible] def ID_AFR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ID_AFR0_EL1
@[reducible] def ICV_RPR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_RPR_EL1
@[reducible] def ICV_PMR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_PMR_EL1
@[reducible] def ICV_IGRPEN1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_IGRPEN1_EL1
@[reducible] def ICV_IGRPEN0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_IGRPEN0_EL1
@[reducible] def ICV_IAR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_IAR1_EL1
@[reducible] def ICV_IAR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_IAR0_EL1
@[reducible] def ICV_HPPIR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_HPPIR1_EL1
@[reducible] def ICV_HPPIR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_HPPIR0_EL1
@[reducible] def ICV_EOIR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_EOIR1_EL1
@[reducible] def ICV_EOIR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_EOIR0_EL1
@[reducible] def ICV_DIR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_DIR_EL1
@[reducible] def ICV_CTLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_CTLR_EL1
@[reducible] def ICV_BPR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_BPR1_EL1
@[reducible] def ICV_BPR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICV_BPR0_EL1
@[reducible] def ICH_VTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICH_VTR_EL2
@[reducible] def ICH_VMCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICH_VMCR_EL2
@[reducible] def ICH_MISR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICH_MISR_EL2
@[reducible] def ICH_HCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICH_HCR_EL2
@[reducible] def ICH_ELRSR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICH_ELRSR_EL2
@[reducible] def ICH_EISR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICH_EISR_EL2
@[reducible] def ICC_SRE_EL1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_SRE_EL1_S
@[reducible] def ICC_SRE_EL1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_SRE_EL1_NS
@[reducible] def _ICC_SGI1R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._ICC_SGI1R
@[reducible] def ICC_SGI1R_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_SGI1R_EL1
@[reducible] def _ICC_SGI0R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._ICC_SGI0R
@[reducible] def ICC_SGI0R_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_SGI0R_EL1
@[reducible] def ICC_RPR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_RPR_EL1
@[reducible] def ICC_IGRPEN1_EL1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_IGRPEN1_EL1_S
@[reducible] def ICC_IGRPEN1_EL1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_IGRPEN1_EL1_NS
@[reducible] def ICC_IGRPEN0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_IGRPEN0_EL1
@[reducible] def ICC_IAR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_IAR1_EL1
@[reducible] def ICC_IAR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_IAR0_EL1
@[reducible] def ICC_SRE_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_SRE_EL2
@[reducible] def ICC_HPPIR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_HPPIR1_EL1
@[reducible] def ICC_HPPIR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_HPPIR0_EL1
@[reducible] def ICC_EOIR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_EOIR1_EL1
@[reducible] def ICC_EOIR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_EOIR0_EL1
@[reducible] def ICC_DIR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_DIR_EL1
@[reducible] def ICC_CTLR_EL1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_CTLR_EL1_S
@[reducible] def ICC_CTLR_EL1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_CTLR_EL1_NS
@[reducible] def ICC_BPR1_EL1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_BPR1_EL1_S
@[reducible] def ICC_BPR1_EL1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_BPR1_EL1_NS
@[reducible] def ICC_BPR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_BPR0_EL1
@[reducible] def _ICC_ASGI1R : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._ICC_ASGI1R
@[reducible] def ICC_ASGI1R_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_ASGI1R_EL1
@[reducible] def TRFCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TRFCR_EL2
@[reducible] def HSTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HSTR_EL2
@[reducible] def RMR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RMR_EL2
@[reducible] def ERRSELR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERRSELR_EL1
@[reducible] def ERRIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ERRIDR_EL1
@[reducible] def DBGVCR32_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGVCR32_EL2
@[reducible] def _DBGDRAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._DBGDRAR
@[reducible] def MDRAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDRAR_EL1
@[reducible] def MDCCINT_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDCCINT_EL1
@[reducible] def DBGCLAIMSET_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGCLAIMSET_EL1
@[reducible] def DBGCLAIMCLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGCLAIMCLR_EL1
@[reducible] def DBGAUTHSTATUS_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGAUTHSTATUS_EL1
@[reducible] def CSSELR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CSSELR_EL1
@[reducible] def CCSIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CCSIDR_EL1
@[reducible] def CCSIDR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CCSIDR2_EL1
@[reducible] def AMUSERENR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMUSERENR_EL0
@[reducible] def AMCR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCR_EL0
@[reducible] def AMCNTENSET1_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCNTENSET1_EL0
@[reducible] def AMCNTENSET0_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCNTENSET0_EL0
@[reducible] def AMCNTENCLR1_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCNTENCLR1_EL0
@[reducible] def AMCNTENCLR0_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCNTENCLR0_EL0
@[reducible] def AMCGCR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCGCR_EL0
@[reducible] def AMCFGR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .AMCFGR_EL0
@[reducible] def PMVCIDSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMVCIDSR
@[reducible] def PMPCSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMPCSR
@[reducible] def PMPCSCTL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMPCSCTL
@[reducible] def PMIIDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMIIDR
@[reducible] def PMCFGR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCFGR
@[reducible] def GITS_TYPER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GITS_TYPER
@[reducible] def GITS_SGIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GITS_SGIR
@[reducible] def GITS_CWRITER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GITS_CWRITER
@[reducible] def GITS_CREADR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GITS_CREADR
@[reducible] def GITS_CBASER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GITS_CBASER
@[reducible] def GICR_VPROPBASER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_VPROPBASER
@[reducible] def GICR_VPENDBASER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_VPENDBASER
@[reducible] def GICR_SETLPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_SETLPIR
@[reducible] def GICR_PROPBASER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_PROPBASER
@[reducible] def GICR_PENDBASER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_PENDBASER
@[reducible] def GICR_INVLPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_INVLPIR
@[reducible] def GICR_INVALLR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_INVALLR
@[reducible] def GICR_CLRLPIR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GICR_CLRLPIR
@[reducible] def EDPFR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDPFR
@[reducible] def EDPCSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDPCSR
@[reducible] def EDHSR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDHSR
@[reducible] def EDDFR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDDFR1
@[reducible] def EDDFR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDDFR
@[reducible] def EDAA32PFR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDAA32PFR
@[reducible] def DBGDSAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGDSAR
@[reducible] def RVBAR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RVBAR_EL3
@[reducible] def RVBAR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RVBAR_EL2
@[reducible] def RVBAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RVBAR_EL1
@[reducible] def VDISR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VDISR_EL2
@[reducible] def VSESR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VSESR_EL2
@[reducible] def DISR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DISR_EL1
@[reducible] def HFGITR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HFGITR_EL2
@[reducible] def VNCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VNCR_EL2
@[reducible] def VMECID_A_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VMECID_A_EL2
@[reducible] def S2POR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .S2POR_EL1
@[reducible] def VSTTBR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VSTTBR_EL2
@[reducible] def VSTCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VSTCR_EL2
@[reducible] def S2PIR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .S2PIR_EL2
@[reducible] def MECID_RL_A_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MECID_RL_A_EL3
@[reducible] def MECID_P1_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MECID_P1_EL2
@[reducible] def MECID_A1_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MECID_A1_EL2
@[reducible] def MECID_A0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MECID_A0_EL2
@[reducible] def VMECID_P_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VMECID_P_EL2
@[reducible] def MECID_P0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MECID_P0_EL2
@[reducible] def POR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .POR_EL0
@[reducible] def POR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .POR_EL3
@[reducible] def POR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .POR_EL2
@[reducible] def POR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .POR_EL1
@[reducible] def EDWAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .EDWAR
@[reducible] def VTTBR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VTTBR
@[reducible] def VTCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VTCR_EL2
@[reducible] def CONTEXTIDR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CONTEXTIDR_EL2
@[reducible] def TFSR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TFSR_EL3
@[reducible] def TFSR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TFSR_EL2
@[reducible] def TFSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TFSR_EL1
@[reducible] def TFSRE0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TFSRE0_EL1
@[reducible] def RGSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .RGSR_EL1
@[reducible] def GCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCR_EL1
@[reducible] def APGAKeyLo_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APGAKeyLo_EL1
@[reducible] def APGAKeyHi_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APGAKeyHi_EL1
@[reducible] def APDBKeyLo_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APDBKeyLo_EL1
@[reducible] def APDBKeyHi_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APDBKeyHi_EL1
@[reducible] def APDAKeyLo_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APDAKeyLo_EL1
@[reducible] def APDAKeyHi_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APDAKeyHi_EL1
@[reducible] def APIBKeyLo_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APIBKeyLo_EL1
@[reducible] def APIBKeyHi_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APIBKeyHi_EL1
@[reducible] def APIAKeyLo_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APIAKeyLo_EL1
@[reducible] def APIAKeyHi_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .APIAKeyHi_EL1
@[reducible] def TTBR0_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TTBR0_EL3
@[reducible] def SCTLR2_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCTLR2_EL3
@[reducible] def PIR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PIR_EL3
@[reducible] def MAIR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MAIR_EL3
@[reducible] def MAIR2_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MAIR2_EL3
@[reducible] def PIRE0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PIRE0_EL2
@[reducible] def TCR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TCR2_EL2
@[reducible] def PIR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PIR_EL2
@[reducible] def MAIR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MAIR_EL2
@[reducible] def MAIR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MAIR2_EL2
@[reducible] def TCR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TCR2_EL1
@[reducible] def PIR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PIR_EL1
@[reducible] def PIRE0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PIRE0_EL1
@[reducible] def MAIR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MAIR_EL1
@[reducible] def MAIR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MAIR2_EL1
@[reducible] def GPTBR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GPTBR_EL3
@[reducible] def GPCCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GPCCR_EL3
@[reducible] def CNTKCTL_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTKCTL_EL1
@[reducible] def CNTPS_CVAL_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTPS_CVAL_EL1
@[reducible] def CNTPS_CTL_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTPS_CTL_EL1
@[reducible] def CNTHV_CVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHV_CVAL_EL2
@[reducible] def CNTHV_CTL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHV_CTL_EL2
@[reducible] def CNTHVS_CVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHVS_CVAL_EL2
@[reducible] def CNTHVS_CTL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHVS_CTL_EL2
@[reducible] def CNTHPS_CVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHPS_CVAL_EL2
@[reducible] def CNTHPS_CTL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHPS_CTL_EL2
@[reducible] def CNTV_CVAL_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTV_CVAL_EL0
@[reducible] def CNTV_CTL_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTV_CTL_EL0
@[reducible] def CNTP_CVAL_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTP_CVAL_S
@[reducible] def _CNTP_CVAL_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._CNTP_CVAL_NS
@[reducible] def CNTP_CVAL_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTP_CVAL_EL0
@[reducible] def CNTP_CTL_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTP_CTL_EL0
@[reducible] def _CNTHP_CVAL : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._CNTHP_CVAL
@[reducible] def CNTHP_CVAL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHP_CVAL_EL2
@[reducible] def CNTHP_CTL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHP_CTL_EL2
@[reducible] def FPEXC32_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .FPEXC32_EL2
@[reducible] def SCTLR2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCTLR2_EL2
@[reducible] def SCTLR2_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCTLR2_EL1
@[reducible] def IFSR32_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .IFSR32_EL2
@[reducible] def TTBR1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TTBR1_S
@[reducible] def TTBR1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TTBR1_NS
@[reducible] def HTTBR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HTTBR
@[reducible] def TTBR0_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TTBR0_S
@[reducible] def TTBR0_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TTBR0_NS
@[reducible] def CONTEXTIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CONTEXTIDR_EL1
@[reducible] def CLIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CLIDR_EL1
@[reducible] def MPAMSM_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMSM_EL1
@[reducible] def MPAM0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAM0_EL1
@[reducible] def MPAMVPM7_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM7_EL2
@[reducible] def MPAMVPM6_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM6_EL2
@[reducible] def MPAMVPM5_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM5_EL2
@[reducible] def MPAMVPM4_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM4_EL2
@[reducible] def MPAMVPM3_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM3_EL2
@[reducible] def MPAMVPM2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM2_EL2
@[reducible] def MPAMVPM1_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM1_EL2
@[reducible] def MPAMVPMV_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPMV_EL2
@[reducible] def MPAMVPM0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMVPM0_EL2
@[reducible] def MPAMHCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMHCR_EL2
@[reducible] def MPAMIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAMIDR_EL1
@[reducible] def _MPAM1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._MPAM1_EL1
@[reducible] def _MPAM3_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._MPAM3_EL3
@[reducible] def MPAM2_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MPAM2_EL2
@[reducible] def HCRX_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HCRX_EL2
@[reducible] def GCSCRE0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSCRE0_EL1
@[reducible] def VBAR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VBAR_EL3
@[reducible] def VBAR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VBAR_EL2
@[reducible] def VBAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .VBAR_EL1
@[reducible] def OSECCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .OSECCR_EL1
@[reducible] def SPSR_und : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_und
@[reducible] def SPSR_irq : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_irq
@[reducible] def SPSR_fiq : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_fiq
@[reducible] def SPSR_abt : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_abt
@[reducible] def SPSR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_EL3
@[reducible] def SPSR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_EL2
@[reducible] def SPSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPSR_EL1
@[reducible] def ELR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ELR_EL3
@[reducible] def ELR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ELR_EL2
@[reducible] def ELR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ELR_EL1
@[reducible] def PFAR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PFAR_EL2
@[reducible] def PFAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PFAR_EL1
@[reducible] def MFAR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MFAR_EL3
@[reducible] def HPFAR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HPFAR_EL2
@[reducible] def FAR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .FAR_EL3
@[reducible] def FAR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .FAR_EL2
@[reducible] def FAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .FAR_EL1
@[reducible] def ESR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ESR_EL3
@[reducible] def ESR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ESR_EL2
@[reducible] def ESR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ESR_EL1
@[reducible] def SCTLR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCTLR_EL3
@[reducible] def SCTLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCTLR_EL1
@[reducible] def SCTLR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCTLR_EL2
@[reducible] def OSLSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .OSLSR_EL1
@[reducible] def MDSCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDSCR_EL1
@[reducible] def GCSCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSCR_EL3
@[reducible] def GCSCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSCR_EL2
@[reducible] def GCSCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSCR_EL1
@[reducible] def DBGPRCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DBGPRCR_EL1
@[reducible] def OSDLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .OSDLR_EL1
@[reducible] def CPTR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CPTR_EL3
@[reducible] def CPTR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CPTR_EL2
@[reducible] def CPACR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CPACR_EL1
@[reducible] def GCSPR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSPR_EL3
@[reducible] def GCSPR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSPR_EL2
@[reducible] def GCSPR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSPR_EL1
@[reducible] def GCSPR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .GCSPR_EL0
@[reducible] def SMCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SMCR_EL3
@[reducible] def SMCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SMCR_EL2
@[reducible] def SMCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SMCR_EL1
@[reducible] def ZCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ZCR_EL3
@[reducible] def ZCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ZCR_EL2
@[reducible] def ZCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ZCR_EL1
@[reducible] def PMBSR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMBSR_EL1
@[reducible] def PMBLIMITR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMBLIMITR_EL1
@[reducible] def PMSCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSCR_EL2
@[reducible] def PMSCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSCR_EL1
@[reducible] def PMSIDR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMSIDR_EL1
@[reducible] def BRBIDR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBIDR0_EL1
@[reducible] def TCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TCR_EL3
@[reducible] def TCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TCR_EL2
@[reducible] def TCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .TCR_EL1
@[reducible] def DSPSR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DSPSR_EL0
@[reducible] def DLR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .DLR_EL0
@[reducible] def CFG_RVBAR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CFG_RVBAR
@[reducible] def CNTHCTL_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTHCTL_EL2
@[reducible] def CNTVOFF_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTVOFF_EL2
@[reducible] def CNTPOFF_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CNTPOFF_EL2
@[reducible] def BRBTS_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBTS_EL1
@[reducible] def BRBFCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBFCR_EL1
@[reducible] def BRBCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBCR_EL2
@[reducible] def BRBCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .BRBCR_EL1
@[reducible] def PMOVSSET_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMOVSSET_EL0
@[reducible] def PMICNTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMICNTR_EL0
@[reducible] def _SDER32_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 ._SDER32_EL3
@[reducible] def SDER32_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SDER32_EL2
@[reducible] def PMICFILTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMICFILTR_EL0
@[reducible] def PMCNTENSET_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCNTENSET_EL0
@[reducible] def PMCCFILTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCCFILTR_EL0
@[reducible] def MDCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDCR_EL3
@[reducible] def PMOVSCLR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMOVSCLR_EL0
@[reducible] def PMINTENCLR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMINTENCLR_EL1
@[reducible] def PMCR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCR_EL0
@[reducible] def PMCNTENCLR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .PMCNTENCLR_EL0
@[reducible] def MDCCSR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDCCSR_EL0
@[reducible] def MDCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .MDCR_EL2
@[reducible] def CTR_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .CTR_EL0
@[reducible] def SCR_EL3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SCR_EL3
@[reducible] def HCR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .HCR_EL2
@[reducible] def sp_rel_access_pc : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .sp_rel_access_pc
@[reducible] def SPESampleEvents : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPESampleEvents
@[reducible] def SPESampleTimestamp : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPESampleTimestamp
@[reducible] def SPESamplePreviousBranchAddress : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .SPESamplePreviousBranchAddress
@[reducible] def ICC_PMR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64) := Regs.ref_BitVec_64 .ICC_PMR_EL1
@[reducible] def AMEVTYPER1_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) := Regs.ref_Vector_BitVec_64_16 .AMEVTYPER1_EL0
@[reducible] def AMEVCNTVOFF1_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) := Regs.ref_Vector_BitVec_64_16 .AMEVCNTVOFF1_EL2
@[reducible] def _AMEVCNTR1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) := Regs.ref_Vector_BitVec_64_16 ._AMEVCNTR1
@[reducible] def AMEVCNTVOFF0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) := Regs.ref_Vector_BitVec_64_16 .AMEVCNTVOFF0_EL2
@[reducible] def AMEVCNTR1_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) := Regs.ref_Vector_BitVec_64_16 .AMEVCNTR1_EL0
@[reducible] def ICH_LR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16) := Regs.ref_Vector_BitVec_64_16 .ICH_LR_EL2
@[reducible] def _AMEVCNTR0_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 ._AMEVCNTR0_EL0
@[reducible] def AMEVCNTR0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .AMEVCNTR0
@[reducible] def ICV_AP1R_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICV_AP1R_EL1
@[reducible] def ICV_AP0R_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICV_AP0R_EL1
@[reducible] def ICC_AP1R_EL1_NS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICC_AP1R_EL1_NS
@[reducible] def ICC_AP1R_EL1_S : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICC_AP1R_EL1_S
@[reducible] def ICH_AP0R_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICH_AP0R_EL2
@[reducible] def ICH_AP1R_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICH_AP1R_EL2
@[reducible] def ICC_AP0R_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ICC_AP0R_EL1
@[reducible] def AMEVTYPER0_EL0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .AMEVTYPER0_EL0
@[reducible] def ERRnFR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4) := Regs.ref_Vector_BitVec_64_4 .ERRnFR
@[reducible] def _PMEVCNTR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 31) := Regs.ref_Vector_BitVec_32_31 ._PMEVCNTR
@[reducible] def _PMEVTYPER : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 31) := Regs.ref_Vector_BitVec_32_31 ._PMEVTYPER
@[reducible] def __has_spe_pseudo_cycles : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__has_spe_pseudo_cycles
@[reducible] def __mops_forward_copy : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__mops_forward_copy
@[reducible] def __trickbox_enabled : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__trickbox_enabled
@[reducible] def __ignore_rvbar_in_aarch32 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__ignore_rvbar_in_aarch32
@[reducible] def __unpred_tsize_aborts : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__unpred_tsize_aborts
@[reducible] def __syncAbortOnDeviceWrite : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnDeviceWrite
@[reducible] def __syncAbortOnWriteNormNonCache : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnWriteNormNonCache
@[reducible] def __syncAbortOnWriteNormCache : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnWriteNormCache
@[reducible] def __syncAbortOnTTWNonCache : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnTTWNonCache
@[reducible] def __syncAbortOnTTWCache : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnTTWCache
@[reducible] def __syncAbortOnPrefetch : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnPrefetch
@[reducible] def __syncAbortOnSoWrite : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnSoWrite
@[reducible] def __syncAbortOnSoRead : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnSoRead
@[reducible] def __syncAbortOnDeviceRead : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnDeviceRead
@[reducible] def __syncAbortOnReadNormNonCache : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnReadNormNonCache
@[reducible] def __syncAbortOnReadNormCache : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__syncAbortOnReadNormCache
@[reducible] def __mpam_has_altsp : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__mpam_has_altsp
@[reducible] def __tlb_enabled : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__tlb_enabled
@[reducible] def __mpam_has_hcr : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__mpam_has_hcr
@[reducible] def C47_IMPDEF_TRANSACTIONAL_SYSREG_ACCESS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C47_IMPDEF_TRANSACTIONAL_SYSREG_ACCESS
@[reducible] def C40_IMPDEF_BOOL_9 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_9
@[reducible] def C40_IMPDEF_BOOL_6 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_6
@[reducible] def C40_IMPDEF_BOOL_5 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_5
@[reducible] def C40_IMPDEF_BOOL_4 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_4
@[reducible] def C40_IMPDEF_BOOL_3 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_3
@[reducible] def C40_IMPDEF_BOOL_2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_2
@[reducible] def C40_IMPDEF_BOOL_11 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_11
@[reducible] def C40_IMPDEF_BOOL_1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_1
@[reducible] def C40_IMPDEF_BOOL_0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .C40_IMPDEF_BOOL_0
@[reducible] def __sme_only : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__sme_only
@[reducible] def __setg_mops_option_a_supported : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__setg_mops_option_a_supported
@[reducible] def __set_mops_option_a_supported : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__set_mops_option_a_supported
@[reducible] def __isb_is_branch : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__isb_is_branch
@[reducible] def __has_sme_priority_control : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__has_sme_priority_control
@[reducible] def __feat_rpres : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__feat_rpres
@[reducible] def __empam_tidr_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__empam_tidr_implemented
@[reducible] def __empam_sdeflt_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__empam_sdeflt_implemented
@[reducible] def __empam_force_ns_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__empam_force_ns_implemented
@[reducible] def __empam_force_ns_RAO : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__empam_force_ns_RAO
@[reducible] def __cpyf_mops_option_a_supported : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__cpyf_mops_option_a_supported
@[reducible] def __cpy_mops_option_a_supported : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__cpy_mops_option_a_supported
@[reducible] def __apply_effective_shareability : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__apply_effective_shareability
@[reducible] def __highest_el_aarch32 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__highest_el_aarch32
@[reducible] def __ExclusiveMonitorSet : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__ExclusiveMonitorSet
@[reducible] def __InstructionStep : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__InstructionStep
@[reducible] def __last_branch_valid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__last_branch_valid
@[reducible] def __SPE_LFSR_initialized : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .__SPE_LFSR_initialized
@[reducible] def SPESampleTimestampValid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleTimestampValid
@[reducible] def SPESampleSubclassValid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleSubclassValid
@[reducible] def SPESampleDataSourceValid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleDataSourceValid
@[reducible] def SPESamplePreviousBranchAddressValid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESamplePreviousBranchAddressValid
@[reducible] def SPESampleInstIsNV2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleInstIsNV2
@[reducible] def SPESampleContextEL2Valid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleContextEL2Valid
@[reducible] def SPESampleContextEL1Valid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleContextEL1Valid
@[reducible] def SPESampleInFlight : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .SPESampleInFlight
@[reducible] def InGuardedPage : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .InGuardedPage
@[reducible] def IsWFEsleep : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .IsWFEsleep
@[reducible] def IsWFIsleep : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .IsWFIsleep
@[reducible] def v9Ap4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v9Ap4_IMPLEMENTED
@[reducible] def v9Ap3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v9Ap3_IMPLEMENTED
@[reducible] def v9Ap2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v9Ap2_IMPLEMENTED
@[reducible] def v9Ap1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v9Ap1_IMPLEMENTED
@[reducible] def v9Ap0_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v9Ap0_IMPLEMENTED
@[reducible] def v8Ap9_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap9_IMPLEMENTED
@[reducible] def v8Ap8_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap8_IMPLEMENTED
@[reducible] def v8Ap7_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap7_IMPLEMENTED
@[reducible] def v8Ap6_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap6_IMPLEMENTED
@[reducible] def v8Ap5_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap5_IMPLEMENTED
@[reducible] def v8Ap4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap4_IMPLEMENTED
@[reducible] def v8Ap3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap3_IMPLEMENTED
@[reducible] def v8Ap2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap2_IMPLEMENTED
@[reducible] def v8Ap1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap1_IMPLEMENTED
@[reducible] def v8Ap0_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .v8Ap0_IMPLEMENTED
@[reducible] def FEAT_TRBE_MPAM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TRBE_MPAM_IMPLEMENTED
@[reducible] def FEAT_TRBE_EXT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TRBE_EXT_IMPLEMENTED
@[reducible] def FEAT_SYSREG128_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SYSREG128_IMPLEMENTED
@[reducible] def FEAT_SYSINSTR128_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SYSINSTR128_IMPLEMENTED
@[reducible] def FEAT_SVE_B16B16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_B16B16_IMPLEMENTED
@[reducible] def FEAT_SVE2p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE2p1_IMPLEMENTED
@[reducible] def FEAT_SME_F16F16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME_F16F16_IMPLEMENTED
@[reducible] def FEAT_SME2p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME2p1_IMPLEMENTED
@[reducible] def FEAT_SEBEP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SEBEP_IMPLEMENTED
@[reducible] def FEAT_LVA3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LVA3_IMPLEMENTED
@[reducible] def FEAT_LSE128_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LSE128_IMPLEMENTED
@[reducible] def FEAT_ITE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ITE_IMPLEMENTED
@[reducible] def FEAT_GCS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GCS_IMPLEMENTED
@[reducible] def FEAT_ETEv1p3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETEv1p3_IMPLEMENTED
@[reducible] def FEAT_EBEP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EBEP_IMPLEMENTED
@[reducible] def FEAT_D128_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_D128_IMPLEMENTED
@[reducible] def FEAT_CHK_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CHK_IMPLEMENTED
@[reducible] def FEAT_ABLE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ABLE_IMPLEMENTED
@[reducible] def FEAT_SME2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME2_IMPLEMENTED
@[reducible] def FEAT_MEC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MEC_IMPLEMENTED
@[reducible] def FEAT_BRBEv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_BRBEv1p1_IMPLEMENTED
@[reducible] def FEAT_SME_I16I64_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME_I16I64_IMPLEMENTED
@[reducible] def FEAT_SME_FA64_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME_FA64_IMPLEMENTED
@[reducible] def FEAT_SME_F64F64_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME_F64F64_IMPLEMENTED
@[reducible] def FEAT_SME_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SME_IMPLEMENTED
@[reducible] def FEAT_RME_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RME_IMPLEMENTED
@[reducible] def FEAT_ETEv1p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETEv1p2_IMPLEMENTED
@[reducible] def FEAT_BRBE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_BRBE_IMPLEMENTED
@[reducible] def FEAT_ETEv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETEv1p1_IMPLEMENTED
@[reducible] def FEAT_TRBE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TRBE_IMPLEMENTED
@[reducible] def FEAT_TME_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TME_IMPLEMENTED
@[reducible] def FEAT_SVE_SM4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_SM4_IMPLEMENTED
@[reducible] def FEAT_SVE_SHA3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_SHA3_IMPLEMENTED
@[reducible] def FEAT_SVE_PMULL128_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_PMULL128_IMPLEMENTED
@[reducible] def FEAT_SVE_BitPerm_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_BitPerm_IMPLEMENTED
@[reducible] def FEAT_SVE_AES_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_AES_IMPLEMENTED
@[reducible] def FEAT_SVE2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE2_IMPLEMENTED
@[reducible] def FEAT_ETE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETE_IMPLEMENTED
@[reducible] def FEAT_DoPD_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DoPD_IMPLEMENTED
@[reducible] def FEAT_THE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_THE_IMPLEMENTED
@[reducible] def FEAT_SPMU_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPMU_IMPLEMENTED
@[reducible] def FEAT_SPEv1p4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPEv1p4_IMPLEMENTED
@[reducible] def FEAT_SPE_FDS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPE_FDS_IMPLEMENTED
@[reducible] def FEAT_SPE_CRR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPE_CRR_IMPLEMENTED
@[reducible] def FEAT_SPECRES2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPECRES2_IMPLEMENTED
@[reducible] def FEAT_S2POE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_S2POE_IMPLEMENTED
@[reducible] def FEAT_S2PIE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_S2PIE_IMPLEMENTED
@[reducible] def FEAT_S1POE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_S1POE_IMPLEMENTED
@[reducible] def FEAT_S1PIE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_S1PIE_IMPLEMENTED
@[reducible] def FEAT_RPRFM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RPRFM_IMPLEMENTED
@[reducible] def FEAT_RASv2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RASv2_IMPLEMENTED
@[reducible] def FEAT_RASSAv2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RASSAv2_IMPLEMENTED
@[reducible] def FEAT_PRFMSLC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PRFMSLC_IMPLEMENTED
@[reducible] def FEAT_PMUv3p9_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3p9_IMPLEMENTED
@[reducible] def FEAT_PMUv3_SS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_SS_IMPLEMENTED
@[reducible] def FEAT_PMUv3_ICNTR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_ICNTR_IMPLEMENTED
@[reducible] def FEAT_PMUv3_EDGE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_EDGE_IMPLEMENTED
@[reducible] def FEAT_PFAR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PFAR_IMPLEMENTED
@[reducible] def FEAT_PCSRv8p9_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PCSRv8p9_IMPLEMENTED
@[reducible] def FEAT_MTE_TAGGED_FAR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_TAGGED_FAR_IMPLEMENTED
@[reducible] def FEAT_MTE_STORE_ONLY_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_STORE_ONLY_IMPLEMENTED
@[reducible] def FEAT_MTE_PERM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_PERM_IMPLEMENTED
@[reducible] def FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED
@[reducible] def FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED
@[reducible] def FEAT_MTE_ASYNC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_ASYNC_IMPLEMENTED
@[reducible] def FEAT_MTE_ASYM_FAULT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_ASYM_FAULT_IMPLEMENTED
@[reducible] def FEAT_MTE4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE4_IMPLEMENTED
@[reducible] def FEAT_LRCPC3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LRCPC3_IMPLEMENTED
@[reducible] def FEAT_HAFT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HAFT_IMPLEMENTED
@[reducible] def FEAT_FGT2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FGT2_IMPLEMENTED
@[reducible] def FEAT_ECBHB_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ECBHB_IMPLEMENTED
@[reducible] def FEAT_DoubleFault2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DoubleFault2_IMPLEMENTED
@[reducible] def FEAT_Debugv8p9_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_Debugv8p9_IMPLEMENTED
@[reducible] def FEAT_CSSC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSSC_IMPLEMENTED
@[reducible] def FEAT_CLRBHB_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CLRBHB_IMPLEMENTED
@[reducible] def FEAT_ANERR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ANERR_IMPLEMENTED
@[reducible] def FEAT_AIE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AIE_IMPLEMENTED
@[reducible] def FEAT_ADERR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ADERR_IMPLEMENTED
@[reducible] def FEAT_TIDCP1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TIDCP1_IMPLEMENTED
@[reducible] def FEAT_TCR2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TCR2_IMPLEMENTED
@[reducible] def FEAT_SPEv1p3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPEv1p3_IMPLEMENTED
@[reducible] def FEAT_SCTLR2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SCTLR2_IMPLEMENTED
@[reducible] def FEAT_PMUv3p8_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3p8_IMPLEMENTED
@[reducible] def FEAT_PMUv3_TH_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_TH_IMPLEMENTED
@[reducible] def FEAT_PMUv3_EXT64_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_EXT64_IMPLEMENTED
@[reducible] def FEAT_NMI_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_NMI_IMPLEMENTED
@[reducible] def FEAT_MOPS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MOPS_IMPLEMENTED
@[reducible] def FEAT_HBC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HBC_IMPLEMENTED
@[reducible] def FEAT_GICv3_NMI_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv3_NMI_IMPLEMENTED
@[reducible] def FEAT_Debugv8p8_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_Debugv8p8_IMPLEMENTED
@[reducible] def FEAT_CMOW_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CMOW_IMPLEMENTED
@[reducible] def FEAT_XS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_XS_IMPLEMENTED
@[reducible] def FEAT_WFxT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_WFxT_IMPLEMENTED
@[reducible] def FEAT_SPEv1p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPEv1p2_IMPLEMENTED
@[reducible] def FEAT_RPRES_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RPRES_IMPLEMENTED
@[reducible] def FEAT_PMUv3p7_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3p7_IMPLEMENTED
@[reducible] def FEAT_PAN3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PAN3_IMPLEMENTED
@[reducible] def FEAT_MTE3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE3_IMPLEMENTED
@[reducible] def FEAT_LS64_V_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LS64_V_IMPLEMENTED
@[reducible] def FEAT_LS64_ACCDATA_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LS64_ACCDATA_IMPLEMENTED
@[reducible] def FEAT_LS64_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LS64_IMPLEMENTED
@[reducible] def FEAT_LPA2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LPA2_IMPLEMENTED
@[reducible] def FEAT_HCX_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HCX_IMPLEMENTED
@[reducible] def FEAT_EBF16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EBF16_IMPLEMENTED
@[reducible] def FEAT_AFP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AFP_IMPLEMENTED
@[reducible] def FEAT_TWED_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TWED_IMPLEMENTED
@[reducible] def FEAT_PAuth2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PAuth2_IMPLEMENTED
@[reducible] def FEAT_MTPMU_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTPMU_IMPLEMENTED
@[reducible] def FEAT_MPAMv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MPAMv1p1_IMPLEMENTED
@[reducible] def FEAT_MPAMv0p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MPAMv0p1_IMPLEMENTED
@[reducible] def FEAT_HPMN0_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HPMN0_IMPLEMENTED
@[reducible] def FEAT_FGT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FGT_IMPLEMENTED
@[reducible] def FEAT_ECV_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ECV_IMPLEMENTED
@[reducible] def FEAT_DGH_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DGH_IMPLEMENTED
@[reducible] def FEAT_BF16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_BF16_IMPLEMENTED
@[reducible] def FEAT_AMUv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AMUv1p1_IMPLEMENTED
@[reducible] def FEAT_SSBS2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SSBS2_IMPLEMENTED
@[reducible] def FEAT_SSBS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SSBS_IMPLEMENTED
@[reducible] def FEAT_SPECRES_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPECRES_IMPLEMENTED
@[reducible] def FEAT_SB_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SB_IMPLEMENTED
@[reducible] def FEAT_RNG_TRAP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RNG_TRAP_IMPLEMENTED
@[reducible] def FEAT_RNG_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RNG_IMPLEMENTED
@[reducible] def FEAT_PMUv3p5_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3p5_IMPLEMENTED
@[reducible] def FEAT_MTE2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE2_IMPLEMENTED
@[reducible] def FEAT_MTE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MTE_IMPLEMENTED
@[reducible] def FEAT_GTG_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GTG_IMPLEMENTED
@[reducible] def FEAT_FlagM2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FlagM2_IMPLEMENTED
@[reducible] def FEAT_FRINTTS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FRINTTS_IMPLEMENTED
@[reducible] def FEAT_ExS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ExS_IMPLEMENTED
@[reducible] def FEAT_EVT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EVT_IMPLEMENTED
@[reducible] def FEAT_E0PD_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_E0PD_IMPLEMENTED
@[reducible] def FEAT_DPB2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DPB2_IMPLEMENTED
@[reducible] def FEAT_CSV3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSV3_IMPLEMENTED
@[reducible] def FEAT_CSV2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSV2_IMPLEMENTED
@[reducible] def FEAT_BTI_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_BTI_IMPLEMENTED
@[reducible] def FEAT_TTST_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TTST_IMPLEMENTED
@[reducible] def FEAT_TTL_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TTL_IMPLEMENTED
@[reducible] def FEAT_TRF_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TRF_IMPLEMENTED
@[reducible] def FEAT_TLBIRANGE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TLBIRANGE_IMPLEMENTED
@[reducible] def FEAT_TLBIOS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TLBIOS_IMPLEMENTED
@[reducible] def FEAT_SEL2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SEL2_IMPLEMENTED
@[reducible] def FEAT_S2FWB_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_S2FWB_IMPLEMENTED
@[reducible] def FEAT_RASv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RASv1p1_IMPLEMENTED
@[reducible] def FEAT_RASSAv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RASSAv1p1_IMPLEMENTED
@[reducible] def FEAT_PMUv3p4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3p4_IMPLEMENTED
@[reducible] def FEAT_NV2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_NV2_IMPLEMENTED
@[reducible] def FEAT_LSE2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LSE2_IMPLEMENTED
@[reducible] def FEAT_LRCPC2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LRCPC2_IMPLEMENTED
@[reducible] def FEAT_IDST_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_IDST_IMPLEMENTED
@[reducible] def FEAT_FlagM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FlagM_IMPLEMENTED
@[reducible] def FEAT_FHM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FHM_IMPLEMENTED
@[reducible] def FEAT_DoubleFault_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DoubleFault_IMPLEMENTED
@[reducible] def FEAT_DotProd_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DotProd_IMPLEMENTED
@[reducible] def FEAT_Debugv8p4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_Debugv8p4_IMPLEMENTED
@[reducible] def FEAT_DIT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DIT_IMPLEMENTED
@[reducible] def FEAT_CNTSC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CNTSC_IMPLEMENTED
@[reducible] def FEAT_BBM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_BBM_IMPLEMENTED
@[reducible] def FEAT_AMUv1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AMUv1_IMPLEMENTED
@[reducible] def FEAT_SPEv1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPEv1p1_IMPLEMENTED
@[reducible] def FEAT_PAuth_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PAuth_IMPLEMENTED
@[reducible] def FEAT_PACQARMA5_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PACQARMA5_IMPLEMENTED
@[reducible] def FEAT_PACQARMA3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PACQARMA3_IMPLEMENTED
@[reducible] def FEAT_PACIMP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PACIMP_IMPLEMENTED
@[reducible] def FEAT_NV_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_NV_IMPLEMENTED
@[reducible] def FEAT_LRCPC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LRCPC_IMPLEMENTED
@[reducible] def FEAT_JSCVT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_JSCVT_IMPLEMENTED
@[reducible] def FEAT_FPACCOMBINE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FPACCOMBINE_IMPLEMENTED
@[reducible] def FEAT_FPAC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FPAC_IMPLEMENTED
@[reducible] def FEAT_FCMA_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FCMA_IMPLEMENTED
@[reducible] def FEAT_EPAC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EPAC_IMPLEMENTED
@[reducible] def FEAT_CONSTPACFIELD_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CONSTPACFIELD_IMPLEMENTED
@[reducible] def FEAT_CCIDX_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CCIDX_IMPLEMENTED
@[reducible] def FEAT_XNX_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_XNX_IMPLEMENTED
@[reducible] def FEAT_VPIPT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_VPIPT_IMPLEMENTED
@[reducible] def FEAT_UAO_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_UAO_IMPLEMENTED
@[reducible] def FEAT_TTCNP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TTCNP_IMPLEMENTED
@[reducible] def FEAT_SVE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SVE_IMPLEMENTED
@[reducible] def FEAT_SPE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SPE_IMPLEMENTED
@[reducible] def FEAT_SM4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SM4_IMPLEMENTED
@[reducible] def FEAT_SM3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SM3_IMPLEMENTED
@[reducible] def FEAT_SHA512_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SHA512_IMPLEMENTED
@[reducible] def FEAT_SHA3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SHA3_IMPLEMENTED
@[reducible] def FEAT_RAS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RAS_IMPLEMENTED
@[reducible] def FEAT_PCSRv8p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PCSRv8p2_IMPLEMENTED
@[reducible] def FEAT_PAN2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PAN2_IMPLEMENTED
@[reducible] def FEAT_MPAM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_MPAM_IMPLEMENTED
@[reducible] def FEAT_LVA_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LVA_IMPLEMENTED
@[reducible] def FEAT_LSMAOC_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LSMAOC_IMPLEMENTED
@[reducible] def FEAT_LPA_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LPA_IMPLEMENTED
@[reducible] def FEAT_IESB_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_IESB_IMPLEMENTED
@[reducible] def FEAT_I8MM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_I8MM_IMPLEMENTED
@[reducible] def FEAT_HPDS2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HPDS2_IMPLEMENTED
@[reducible] def FEAT_FP16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FP16_IMPLEMENTED
@[reducible] def FEAT_F64MM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_F64MM_IMPLEMENTED
@[reducible] def FEAT_F32MM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_F32MM_IMPLEMENTED
@[reducible] def FEAT_EDHSR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EDHSR_IMPLEMENTED
@[reducible] def FEAT_Debugv8p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_Debugv8p2_IMPLEMENTED
@[reducible] def FEAT_DPB_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DPB_IMPLEMENTED
@[reducible] def FEAT_ASMv8p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ASMv8p2_IMPLEMENTED
@[reducible] def FEAT_AA32I8MM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32I8MM_IMPLEMENTED
@[reducible] def FEAT_AA32HPD_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32HPD_IMPLEMENTED
@[reducible] def FEAT_AA32BF16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32BF16_IMPLEMENTED
@[reducible] def FEAT_VMID16_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_VMID16_IMPLEMENTED
@[reducible] def FEAT_VHE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_VHE_IMPLEMENTED
@[reducible] def FEAT_RDM_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_RDM_IMPLEMENTED
@[reducible] def FEAT_PMUv3p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3p1_IMPLEMENTED
@[reducible] def FEAT_PAN_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PAN_IMPLEMENTED
@[reducible] def FEAT_LSE_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LSE_IMPLEMENTED
@[reducible] def FEAT_LOR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_LOR_IMPLEMENTED
@[reducible] def FEAT_HPDS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HPDS_IMPLEMENTED
@[reducible] def FEAT_HAFDBS_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_HAFDBS_IMPLEMENTED
@[reducible] def FEAT_Debugv8p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_Debugv8p1_IMPLEMENTED
@[reducible] def FEAT_CRC32_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CRC32_IMPLEMENTED
@[reducible] def FEAT_nTLBPA_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_nTLBPA_IMPLEMENTED
@[reducible] def FEAT_TRC_SR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TRC_SR_IMPLEMENTED
@[reducible] def FEAT_TRC_EXT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_TRC_EXT_IMPLEMENTED
@[reducible] def FEAT_SHA256_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SHA256_IMPLEMENTED
@[reducible] def FEAT_SHA1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_SHA1_IMPLEMENTED
@[reducible] def FEAT_PMUv3_EXT32_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_EXT32_IMPLEMENTED
@[reducible] def FEAT_PMUv3_EXT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_EXT_IMPLEMENTED
@[reducible] def FEAT_PMUv3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMUv3_IMPLEMENTED
@[reducible] def FEAT_PMULL_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PMULL_IMPLEMENTED
@[reducible] def FEAT_PCSRv8_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_PCSRv8_IMPLEMENTED
@[reducible] def FEAT_IVIPT_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_IVIPT_IMPLEMENTED
@[reducible] def FEAT_GICv4p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv4p1_IMPLEMENTED
@[reducible] def FEAT_GICv4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv4_IMPLEMENTED
@[reducible] def FEAT_GICv3p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv3p1_IMPLEMENTED
@[reducible] def FEAT_GICv3_TDIR_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv3_TDIR_IMPLEMENTED
@[reducible] def FEAT_GICv3_LEGACY_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv3_LEGACY_IMPLEMENTED
@[reducible] def FEAT_GICv3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_GICv3_IMPLEMENTED
@[reducible] def FEAT_FP_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_FP_IMPLEMENTED
@[reducible] def FEAT_ETS2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETS2_IMPLEMENTED
@[reducible] def FEAT_ETMv4p6_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4p6_IMPLEMENTED
@[reducible] def FEAT_ETMv4p5_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4p5_IMPLEMENTED
@[reducible] def FEAT_ETMv4p4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4p4_IMPLEMENTED
@[reducible] def FEAT_ETMv4p3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4p3_IMPLEMENTED
@[reducible] def FEAT_ETMv4p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4p2_IMPLEMENTED
@[reducible] def FEAT_ETMv4p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4p1_IMPLEMENTED
@[reducible] def FEAT_ETMv4_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_ETMv4_IMPLEMENTED
@[reducible] def FEAT_DoubleLock_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_DoubleLock_IMPLEMENTED
@[reducible] def FEAT_CSV2_3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSV2_3_IMPLEMENTED
@[reducible] def FEAT_CSV2_2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSV2_2_IMPLEMENTED
@[reducible] def FEAT_CSV2_1p2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSV2_1p2_IMPLEMENTED
@[reducible] def FEAT_CSV2_1p1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_CSV2_1p1_IMPLEMENTED
@[reducible] def FEAT_AdvSIMD_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AdvSIMD_IMPLEMENTED
@[reducible] def FEAT_AES_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AES_IMPLEMENTED
@[reducible] def FEAT_EL3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EL3_IMPLEMENTED
@[reducible] def FEAT_EL2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EL2_IMPLEMENTED
@[reducible] def FEAT_EL1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EL1_IMPLEMENTED
@[reducible] def FEAT_EL0_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_EL0_IMPLEMENTED
@[reducible] def FEAT_AA64EL3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA64EL3_IMPLEMENTED
@[reducible] def FEAT_AA64EL2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA64EL2_IMPLEMENTED
@[reducible] def FEAT_AA64EL1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA64EL1_IMPLEMENTED
@[reducible] def FEAT_AA64EL0_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA64EL0_IMPLEMENTED
@[reducible] def FEAT_AA32EL3_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32EL3_IMPLEMENTED
@[reducible] def FEAT_AA32EL2_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32EL2_IMPLEMENTED
@[reducible] def FEAT_AA32EL1_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32EL1_IMPLEMENTED
@[reducible] def FEAT_AA32EL0_IMPLEMENTED : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool := Regs.ref_Bool .FEAT_AA32EL0_IMPLEMENTED
@[reducible] def SMCR_EL3_LEN_VALUE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .SMCR_EL3_LEN_VALUE
@[reducible] def CPTR_EL3_ESM_VALUE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .CPTR_EL3_ESM_VALUE
@[reducible] def CPTR_EL3_EZ_VALUE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .CPTR_EL3_EZ_VALUE
@[reducible] def ZCR_EL3_LEN_VALUE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .ZCR_EL3_LEN_VALUE
@[reducible] def __supported_va_size : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__supported_va_size
@[reducible] def __gmid_log2_block_size : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__gmid_log2_block_size
@[reducible] def __dczid_log2_block_size : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__dczid_log2_block_size
@[reducible] def __supported_pa_size : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__supported_pa_size
@[reducible] def __max_implemented_sveveclen : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__max_implemented_sveveclen
@[reducible] def __max_implemented_smeveclen : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__max_implemented_smeveclen
@[reducible] def __has_sve_extended_bf16 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__has_sve_extended_bf16
@[reducible] def __block_bbm_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__block_bbm_implemented
@[reducible] def __last_cycle_count : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__last_cycle_count
@[reducible] def SPERecordSize : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .SPERecordSize
@[reducible] def __clock_divider : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__clock_divider
@[reducible] def __cycle_count : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__cycle_count
@[reducible] def NUM_GIC_LIST_REGS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_GIC_LIST_REGS
@[reducible] def NUM_GIC_PRIORITY_BITS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_GIC_PRIORITY_BITS
@[reducible] def NUM_GIC_PREEMPTION_BITS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_GIC_PREEMPTION_BITS
@[reducible] def NUM_BRBE_RECORDS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_BRBE_RECORDS
@[reducible] def NUM_PMU_COUNTERS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_PMU_COUNTERS
@[reducible] def NUM_AMU_CG1_MONITORS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_AMU_CG1_MONITORS
@[reducible] def NUM_AMU_CG0_MONITORS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_AMU_CG0_MONITORS
@[reducible] def NUM_AMU_COUNTER_GROUPS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_AMU_COUNTER_GROUPS
@[reducible] def __num_ctx_breakpoints : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .__num_ctx_breakpoints
@[reducible] def NUM_WATCHPOINTS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_WATCHPOINTS
@[reducible] def NUM_BREAKPOINTS : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .NUM_BREAKPOINTS
@[reducible] def SEE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int := Regs.ref_Int .SEE
@[reducible] def CFG_RMR_AA64 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 1) := Regs.ref_BitVec_1 .CFG_RMR_AA64
@[reducible] def EventRegister : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 1) := Regs.ref_BitVec_1 .EventRegister
@[reducible] def __DBG_ROM_ADDR : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__DBG_ROM_ADDR
@[reducible] def __PMUBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__PMUBase
@[reducible] def __GICITSControlBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__GICITSControlBase
@[reducible] def __GICDistBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__GICDistBase
@[reducible] def __GICCPUInterfaceBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__GICCPUInterfaceBase
@[reducible] def __ExtDebugBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__ExtDebugBase
@[reducible] def __CNTControlBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__CNTControlBase
@[reducible] def __CTIBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__CTIBase
@[reducible] def __ETEBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__ETEBase
@[reducible] def __VLPI_base : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__VLPI_base
@[reducible] def __SGI_base : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__SGI_base
@[reducible] def __RD_base : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__RD_base
@[reducible] def __CNTCTLBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__CNTCTLBase
@[reducible] def __CNTEL0BaseN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__CNTEL0BaseN
@[reducible] def __CNTBaseN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__CNTBaseN
@[reducible] def __CNTReadBase : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56) := Regs.ref_BitVec_56 .__CNTReadBase
@[reducible] def __g1_activity_monitor_offset_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 16) := Regs.ref_BitVec_16 .__g1_activity_monitor_offset_implemented
@[reducible] def __g1_activity_monitor_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 16) := Regs.ref_BitVec_16 .__g1_activity_monitor_implemented
@[reducible] def __mpam_partid_max : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 16) := Regs.ref_BitVec_16 .__mpam_partid_max
@[reducible] def SPESampleDataSource : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 16) := Regs.ref_BitVec_16 .SPESampleDataSource
@[reducible] def __rme_l0gptsz : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__rme_l0gptsz
@[reducible] def __mecid_width : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__mecid_width
@[reducible] def __exclusive_granule_size : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__exclusive_granule_size
@[reducible] def __mte_implemented : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__mte_implemented
@[reducible] def __mpam_major : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__mpam_major
@[reducible] def __mpam_frac : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__mpam_frac
@[reducible] def __currentCond : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4) := Regs.ref_BitVec_4 .__currentCond
@[reducible] def _PAR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 ._PAR_EL1
@[reducible] def RCWSMASK_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 .RCWSMASK_EL1
@[reducible] def RCWMASK_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 .RCWMASK_EL1
@[reducible] def _VTTBR_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 ._VTTBR_EL2
@[reducible] def TTBR1_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 .TTBR1_EL2
@[reducible] def _TTBR1_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 ._TTBR1_EL1
@[reducible] def _TTBR0_EL2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 ._TTBR0_EL2
@[reducible] def _TTBR0_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128) := Regs.ref_BitVec_128 ._TTBR0_EL1
@[reducible] def SPESampleCounterValid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 32) := Regs.ref_Vector_Bool_32 .SPESampleCounterValid
@[reducible] def SPESampleCounterPending : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 32) := Regs.ref_Vector_Bool_32 .SPESampleCounterPending
@[reducible] def SPESampleAddressValid : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 32) := Regs.ref_Vector_Bool_32 .SPESampleAddressValid
@[reducible] def DBGWVR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .DBGWVR_EL1
@[reducible] def DBGWCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .DBGWCR_EL1
@[reducible] def DBGBVR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .DBGBVR_EL1
@[reducible] def DBGBCR_EL1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .DBGBCR_EL1
@[reducible] def Records_TGT : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .Records_TGT
@[reducible] def Records_SRC : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .Records_SRC
@[reducible] def Records_INF : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64) := Regs.ref_Vector_BitVec_64_64 .Records_INF
@[reducible] def __GIC_Pending : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Option InterruptID) := Regs.ref_Option_InterruptID .__GIC_Pending
@[reducible] def __GIC_Active : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Option InterruptID) := Regs.ref_Option_InterruptID .__GIC_Active
@[reducible] def __mpam_pmg_max : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 8) := Regs.ref_BitVec_8 .__mpam_pmg_max
@[reducible] def SPESampleSubclass : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 8) := Regs.ref_BitVec_8 .SPESampleSubclass
@[reducible] def __impdef_TG1 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 2) := Regs.ref_BitVec_2 .__impdef_TG1
@[reducible] def __impdef_TG0 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 2) := Regs.ref_BitVec_2 .__impdef_TG0
@[reducible] def SPESampleClass : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 2) := Regs.ref_BitVec_2 .SPESampleClass
@[reducible] def __DCACHE_CCSIDR_RESET : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 7) := Regs.ref_Vector_BitVec_64_7 .__DCACHE_CCSIDR_RESET
@[reducible] def __ICACHE_CCSIDR_RESET : Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 7) := Regs.ref_Vector_BitVec_64_7 .__ICACHE_CCSIDR_RESET
@[reducible] def RTPIDEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .RTPIDEN
@[reducible] def RLPIDEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .RLPIDEN
@[reducible] def SPNIDEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .SPNIDEN
@[reducible] def SPIDEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .SPIDEN
@[reducible] def NIDEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .NIDEN
@[reducible] def DBGEN : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .DBGEN
@[reducible] def CP15SDISABLE2 : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .CP15SDISABLE2
@[reducible] def CP15SDISABLE : Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal := Regs.ref_Signal .CP15SDISABLE

end Register
open Register

def pa_bits (bv : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.zeroExtend bv 64)

instance : Arch where
  va_size := 64
  pa := (BitVec 56)
  abort := Fault
  translation := (Option TranslationInfo)
  trans_start := TranslationStartInfo
  trans_end := AddressDescriptor
  fault := (Option FaultRecord)
  tlb_op := TLBIInfo
  cache_op := CacheRecord
  barrier := Barrier
  arch_ak := arm_acc_type
  sys_reg_id := Unit



abbrev SailM := PreSailM Regs oracleChoiceSource exception
abbrev SailME := PreSailME Regs oracleChoiceSource exception



instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs BranchType) where
  default := Register.Branchtypetaken
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs OpType) where
  default := Register.SPESampleOpType
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs ProcState) where
  default := Register.PSTATE
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs Signal) where
  default := Register.CP15SDISABLE
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs TMState) where
  default := Register.TSTATE
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs __InstrEnc) where
  default := Register.__ThisInstrEnc
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 1)) where
  default := Register.EventRegister
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 128)) where
  default := Register._TTBR0_EL1
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 16)) where
  default := Register.SPESampleDataSource
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 2)) where
  default := Register.BTypeNext
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 24)) where
  default := Register.__SPE_LFSR
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 256)) where
  default := Register._FFR
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 3)) where
  default := Register.__mpam_vpmr_max
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 32)) where
  default := Register.__trcclaim_tags
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 4)) where
  default := Register.__currentCond
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 512)) where
  default := Register._ZT0
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 56)) where
  default := Register.__CNTReadBase
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 64)) where
  default := Register.R0
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 8)) where
  default := Register.SPESampleSubclass
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (BitVec 88)) where
  default := Register.PhysicalCount
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs Bool) where
  default := Register.FEAT_AA32EL0_IMPLEMENTED
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs Int) where
  default := Register.SEE
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Option InterruptID)) where
  default := Register.__GIC_Active
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Option (BitVec 32))) where
  default := Register.__emulator_termination_opcode
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 256) 16)) where
  default := Register._P
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 16)) where
  default := Register._DBGBCR
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 16)) where
  default := Register.ICH_LR_EL2
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 16)) where
  default := Register.VariantImplemented
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 2048) 256)) where
  default := Register._ZA
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 259)) where
  default := Register.FeatureImpl
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 31)) where
  default := Register._PMEVTYPER
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 31)) where
  default := Register.PMEVCNTSVR_EL1
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 31)) where
  default := Register.PMULastThresholdValue
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Int 31)) where
  default := Register.PMUEventAccumulator
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 2048) 32)) where
  default := Register._Z
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 32)) where
  default := Register._Dclone
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Bool 32)) where
  default := Register.SPESampleAddressValid
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector Int 32)) where
  default := Register.SPESampleCounter
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 32) 4)) where
  default := Register._ICV_AP0R
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 4)) where
  default := Register.ERRnFR
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 5)) where
  default := Register.RC
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 64)) where
  default := Register.Records_INF
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 8) 64)) where
  default := Register.SPERecordData
instance : Inhabited (Sail.ConcurrencyInterfaceV1.RegisterRef Regs (Vector (BitVec 64) 7)) where
  default := Register.__ICACHE_CCSIDR_RESET