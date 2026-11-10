import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0012
import ArmFull.Fn.M0014
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0156
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185

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

def AArch64_S1TTWParamsEL20 (ss : SecurityState) (varange : VARange) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1267) ()) ) : SailM S1TTWParams )
  let w__2 ← (( do
    if ((← do
         (Have128BitDescriptorExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with d128 := (_get_TCR2_EL2_Type_D128 w__3) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with d128 := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let walkparams ← (( do
    if ((BEq.beq varange VARange_LOWER) : Bool)
    then
      (do
        let w__4 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__5 ← (( do (AArch64_S1DecodeTG0 (_get_TCR_EL2_Type_TG0 w__4)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__5 } : S1TTWParams)
        let w__6 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with txsz := (_get_TCR_EL2_Type_T0SZ w__6) } : S1TTWParams)
        let w__7 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with irgn := (_get_TCR_EL2_Type_IRGN0 w__7) } : S1TTWParams)
        let w__8 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with orgn := (_get_TCR_EL2_Type_ORGN0 w__8) } : S1TTWParams)
        let w__9 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sh := (_get_TCR_EL2_Type_SH0 w__9) } : S1TTWParams)
        let w__10 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with tbi := (_get_TCR_EL2_Type_TBI0 w__10) } : S1TTWParams)
        let w__13 ← (( do
          if ((← do
               (HaveSVE ())) : Bool)
          then (pure true)
          else
            (do
              (HaveTME ())) ) : SailM Bool )
        let w__15 ← (( do
          if (w__13 : Bool)
          then
            (do
              let w__14 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_NFD0 w__14))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with nfd := w__15 } : S1TTWParams)
        let w__16 ← (( do (HavePACExt ()) ) : SailM Bool )
        let w__18 ← (( do
          if (w__16 : Bool)
          then
            (do
              let w__17 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_TBID0 w__17))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with tbid := w__18 } : S1TTWParams)
        let w__19 ← (( do (HaveE0PDExt ()) ) : SailM Bool )
        let w__21 ← (( do
          if (w__19 : Bool)
          then
            (do
              let w__20 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_E0PD0 w__20))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with e0pd := w__21 } : S1TTWParams)
        let w__22 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
        let w__24 ← (( do
          if (w__22 : Bool)
          then
            (do
              let w__23 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_HPD0 w__23))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with hpd := w__24 } : S1TTWParams)
        let w__25 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
        let w__27 ← (( do
          if (w__25 : Bool)
          then
            (do
              let w__26 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_MTX0 w__26))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with mtx := w__27 } : S1TTWParams)
        let w__29 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__28 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR0_EL2_Type_SKL w__28))))
          else (pure (0b00#2)) ) : SailM (BitVec 2) )
        let walkparams := ({ walkparams with skl := w__29 } : S1TTWParams)
        let w__31 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__30 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL2_Type_DisCH0 w__30))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with disch := w__31 } : S1TTWParams)
        (pure (walkparams)))
    else
      (do
        let w__32 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__33 ← (( do (AArch64_S1DecodeTG1 (_get_TCR_EL2_Type_TG1 w__32)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__33 } : S1TTWParams)
        let w__34 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with txsz := (_get_TCR_EL2_Type_T1SZ w__34) } : S1TTWParams)
        let w__35 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with irgn := (_get_TCR_EL2_Type_IRGN1 w__35) } : S1TTWParams)
        let w__36 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with orgn := (_get_TCR_EL2_Type_ORGN1 w__36) } : S1TTWParams)
        let w__37 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sh := (_get_TCR_EL2_Type_SH1 w__37) } : S1TTWParams)
        let w__38 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with tbi := (_get_TCR_EL2_Type_TBI1 w__38) } : S1TTWParams)
        let w__41 ← (( do
          if ((← do
               (HaveSVE ())) : Bool)
          then (pure true)
          else
            (do
              (HaveTME ())) ) : SailM Bool )
        let w__43 ← (( do
          if (w__41 : Bool)
          then
            (do
              let w__42 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_NFD1 w__42))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with nfd := w__43 } : S1TTWParams)
        let w__44 ← (( do (HavePACExt ()) ) : SailM Bool )
        let w__46 ← (( do
          if (w__44 : Bool)
          then
            (do
              let w__45 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_TBID1 w__45))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with tbid := w__46 } : S1TTWParams)
        let w__47 ← (( do (HaveE0PDExt ()) ) : SailM Bool )
        let w__49 ← (( do
          if (w__47 : Bool)
          then
            (do
              let w__48 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_E0PD1 w__48))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with e0pd := w__49 } : S1TTWParams)
        let w__50 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
        let w__52 ← (( do
          if (w__50 : Bool)
          then
            (do
              let w__51 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_HPD1 w__51))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with hpd := w__52 } : S1TTWParams)
        let w__53 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
        let w__55 ← (( do
          if (w__53 : Bool)
          then
            (do
              let w__54 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL2_Type_MTX1 w__54))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with mtx := w__55 } : S1TTWParams)
        let w__57 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__56 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
              (pure ((_get_TTBR1_EL2_Type_SKL w__56))))
          else (pure (0b00#2)) ) : SailM (BitVec 2) )
        let walkparams := ({ walkparams with skl := w__57 } : S1TTWParams)
        let w__59 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__58 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL2_Type_DisCH1 w__58))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with disch := w__59 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__60 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__60) } : S1TTWParams)
  let w__61 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__61 : Bool)
    then
      (do
        let w__62 ← (( do readReg MAIR2_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__62) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__65 ← (( do
    if ((← do
         (HaveAIEExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__67 ← (( do
    if (w__65 : Bool)
    then
      (do
        let w__66 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_AIE w__66))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__67 } : S1TTWParams)
  let w__68 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL2_Type_WXN w__68) } : S1TTWParams)
  let w__69 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL2_Type_IPS w__69) } : S1TTWParams)
  let w__70 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__70) } : S1TTWParams)
  let w__74 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        if ((← do
             let w__71 ← (( do (HaveRME ()) ) : SailM Bool )
             (pure (((! w__71) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (HaveSecureEL2Ext ())))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__74 : Bool)
    then
      (do
        let w__75 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sif := (_get_SCR_EL3_Type_SIF w__75) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with sif := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__76 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__76 : Bool)
    then
      (do
        let w__77 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with ntlsmd := (_get_SCTLR_EL2_Type_nTLSMD w__77) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ntlsmd := 1#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__78 ← (( do (HaveFeatCMOW ()) ) : SailM Bool )
  let w__80 ← (( do
    if (w__78 : Bool)
    then
      (do
        let w__79 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR_EL2_Type_CMOW w__79))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__80 } : S1TTWParams)
  let w__81 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__85 ← (( do
    if (w__81 : Bool)
    then
      (do
        let w__82 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__83 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__84 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__83) == 0#1) : Bool)
          then 21
          else 39
        (pure ((BitVec.slice w__82 (Sail.Int.toNatChecked (w__84)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__85 } : S1TTWParams)
  let w__86 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__90 ← (( do
    if (w__86 : Bool)
    then
      (do
        let w__87 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__88 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__89 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__88) == 0#1) : Bool)
          then 22
          else 40
        (pure ((BitVec.slice w__87 (Sail.Int.toNatChecked (w__89)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__90 } : S1TTWParams)
  let w__92 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__92 : Bool)
    then
      (do
        let w__93 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__94 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__95 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__94) == 0#1) : Bool)
          then 32
          else 59
        let walkparams :=
          ({ walkparams with ds := (BitVec.slice w__93 (Sail.Int.toNatChecked (w__95)) 1) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S1TTWParams := { walkparams with pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__98 ← (( do
          if ((← do
               (HaveS1PIExt ())) : Bool)
          then
            (do
              (IsTCR2EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        let w__100 ← (( do
          if (w__98 : Bool)
          then
            (do
              let w__99 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL2_Type_PIE w__99))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with pie := w__100 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__101 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__101 : Bool)
    then
      (do
        let w__102 ← (( do readReg PIR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__102) } : S1TTWParams)
        let w__103 ← (( do readReg PIRE0_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pire0 := (Mk_S1PIRType w__103) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__104 ← (( do (HavePAN3Ext ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__104 : Bool)
    then
      (do
        let w__106 ← (( do
          if ((walkparams.pie == 0#1) : Bool)
          then
            (do
              let w__105 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EPAN w__105))))
          else (pure (1#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with epan := w__106 } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with epan := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__110 ← (( do
    if ((← do
         (pure ((← do
               (HaveTHExt ())) && ((walkparams.d128 == 0#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__110 : Bool)
    then
      (do
        let w__111 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with pnch := (_get_TCR2_EL2_Type_PnCH w__111) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with pnch := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__115 ← (( do
    if ((← do
         (pure ((← do
               (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__115 : Bool)
    then
      (do
        let w__116 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_TCR2_EL2_Type_HAFT w__116) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__119 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__121 ← (( do
    if (w__119 : Bool)
    then
      (do
        let w__120 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__120))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__121 } : S1TTWParams)
  let w__125 ← (( do
    if ((← do
         (pure ((← do
               (HaveFeatMEC ())) && ((BEq.beq ss SS_Realm) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__125 : Bool)
  then
    (do
      let w__128 ← (( do
        if ((BEq.beq varange VARange_LOWER) : Bool)
        then
          (do
            let w__126 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_TCR2_EL2_Type_AMEC0 w__126))))
        else
          (do
            let w__127 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_TCR2_EL2_Type_AMEC1 w__127)))) ) : SailM (BitVec 1) )
      let walkparams := ({ walkparams with amec := w__128 } : S1TTWParams)
      (pure (walkparams)))
  else
    (let walkparams : S1TTWParams := { walkparams with amec := 0#1 }
    (pure (walkparams)))


def StoreOnlyTagCheckingEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (HaveMTEStoreOnlyExt ()) ) : SailM Bool )
  ArmFull.assert w__0 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22820.32-22820.33"
  let tcso ← (( do (undefined_bitvector_at (← occLabel 1353) 1) ) : SailM (BitVec 1) )
  let questionMark := el
  let tcso ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__1 ← (( do (ELIsInHost el) ) : SailM Bool )
        if ((! w__1) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tcso := ((_get_SCTLR_EL1_Type_TCSO0 w__2) : (BitVec 1))
            (pure (tcso)))
        else
          (do
            let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let tcso := ((_get_SCTLR_EL2_Type_TCSO0 w__3) : (BitVec 1))
            (pure (tcso))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tcso := ((_get_SCTLR_EL1_Type_TCSO w__4) : (BitVec 1))
            (pure (tcso)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let tcso := ((_get_SCTLR_EL2_Type_TCSO w__5) : (BitVec 1))
                (pure (tcso)))
            else
              (do
                let w__6 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                let tcso := ((_get_SCTLR_EL3_Type_TCSO w__6) : (BitVec 1))
                (pure (tcso))))) ) : SailM (BitVec 1) )
  (pure ((tcso == 1#1)))


/-- Type quantifiers: k_N : Nat, k_s2fs1mro : Bool, k_N ≥ 0 -/
def AArch64_S1NextWalkStateTable (currentstate : TTWState) (s2fs1mro : Bool) (regime : Regime) (walkparams : S1TTWParams) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let skl ← (( do (undefined_bitvector_at (← occLabel 1497) 2) ) : SailM (BitVec 2) )
  let nextstate ← (( do (undefined_TTWState (← occLabel 1498) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1499) ()) ) : SailM FullAddress )
  let w__0 ← (( do (AArch64_NextTableBase descriptor walkparams.d128 walkparams.ds walkparams.tgx)
    ) : SailM (BitVec 56) )
  let tablebase := ({ tablebase with address := w__0 } : FullAddress)
  let tablebase ← (( do
    if ((BEq.beq currentstate.baseaddress.paspace PAS_Secure) : Bool)
    then
      (do
        let nstable ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25632.39-25632.40"
              (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 127)])))))
          else
            (do
              ArmFull.assert (63 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25635.38-25635.39"
              (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 63)]))))) ) : SailM
          (BitVec 1) )
        let tablebase : FullAddress :=
          { tablebase with paspace := if ((nstable == 0#1) : Bool)
            then PAS_Secure
            else PAS_NonSecure }
        (pure (tablebase)))
    else
      (let tablebase : FullAddress := { tablebase with paspace := currentstate.baseaddress.paspace }
      (pure (tablebase))) ) : SailM FullAddress )
  let nextstate : TTWState := { nextstate with istable := true }
  let nextstate : TTWState := { nextstate with nG := currentstate.nG }
  let nextstate ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (110 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25645.35-25645.36"
        let skl : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 110 109)
        let nextstate : TTWState :=
          { nextstate with level := ((currentstate.level +i (BitVec.toNat skl)) +i 1) }
        (pure (nextstate)))
    else
      (let nextstate : TTWState := { nextstate with level := (currentstate.level +i 1) }
      (pure (nextstate))) ) : SailM TTWState )
  let nextstate : TTWState := { nextstate with baseaddress := tablebase }
  let nextstate : TTWState := { nextstate with memattrs := currentstate.memattrs }
  let nextstate ← (( do
    if (((walkparams.hpd == 0#1) && (walkparams.pie == 0#1)) : Bool)
    then
      (do
        let w__1 ← (( do
          (AArch64_S1ApplyTablePerms currentstate.permissions descriptor regime walkparams) ) :
          SailM Permissions )
        let nextstate := ({ nextstate with permissions := w__1 } : TTWState)
        (pure (nextstate)))
    else
      (let nextstate : TTWState := { nextstate with permissions := currentstate.permissions }
      (pure (nextstate))) ) : SailM TTWState )
  let protectedbit ← (( do (undefined_bitvector_at (← occLabel 1500) 1) ) : SailM (BitVec 1) )
  let protectedbit ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (114 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25660.35-25660.36"
        let protectedbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 114)]))
        (pure (protectedbit)))
    else
      (do
        if ((walkparams.pnch == 1#1) : Bool)
        then
          (do
            ArmFull.assert (52 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25664.38-25664.39"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 52)])))))
        else (pure (0#1))) ) : SailM (BitVec 1) )
  let nextstate : TTWState :=
    if (((currentstate.s1assured && s2fs1mro) && (protectedbit == 1#1)) : Bool)
    then { nextstate with s1assured := true }
    else { nextstate with s1assured := false }
  let w__3 ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (112 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25674.35-25674.36"
        (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 112)])))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let nextstate := ({ nextstate with disch := w__3 } : TTWState)
  (pure (nextstate))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_NSS2TTWParams (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 1504) ()) ) : SailM S2TTWParams )
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let walkparams :=
    ({ walkparams with vm := ((_get_HCR_EL2_Type_VM w__0) ||| (_get_HCR_EL2_Type_DC w__1)) } : S2TTWParams)
  let w__2 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let w__3 ← (( do (AArch64_S2DecodeTG0 (_get_VTCR_EL2_Type_TG0 w__2)) ) : SailM TGx )
  let walkparams := ({ walkparams with tgx := w__3 } : S2TTWParams)
  let w__4 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with txsz := (_get_VTCR_EL2_Type_T0SZ w__4) } : S2TTWParams)
  let w__5 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_VTCR_EL2_Type_PS w__5) } : S2TTWParams)
  let w__6 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_VTCR_EL2_Type_IRGN0 w__6) } : S2TTWParams)
  let w__7 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_VTCR_EL2_Type_ORGN0 w__7) } : S2TTWParams)
  let w__8 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_VTCR_EL2_Type_SH0 w__8) } : S2TTWParams)
  let w__9 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__9) } : S2TTWParams)
  let w__10 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  let w__12 ← (( do
    if (w__10 : Bool)
    then
      (do
        let w__11 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_D128 w__11))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with d128 := w__12 } : S2TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        let w__13 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
        let walkparams := ({ walkparams with skl := (_get_VTTBR_EL2_Type_SKL w__13) } : S2TTWParams)
        (pure (walkparams)))
    else
      (do
        let w__14 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sl0 := (_get_VTCR_EL2_Type_SL0 w__14) } : S2TTWParams)
        (pure (walkparams))) ) : SailM S2TTWParams )
  let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__17 ← (( do
    if (((_get_HCR_EL2_Type_TGE w__15) == 0#1) : Bool)
    then
      (do
        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_PTW w__16))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ptw := w__17 } : S2TTWParams)
  let w__18 ← (( do (HaveStage2MemAttrControl ()) ) : SailM Bool )
  let w__20 ← (( do
    if (w__18 : Bool)
    then
      (do
        let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_FWB w__19))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with fwb := w__20 } : S2TTWParams)
  let w__21 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__23 ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HA w__22))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__23 } : S2TTWParams)
  let w__24 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__26 ← (( do
    if (w__24 : Bool)
    then
      (do
        let w__25 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HD w__25))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__26 } : S2TTWParams)
  let w__28 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__28 : Bool)
    then
      (do
        let w__29 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_VTCR_EL2_Type_DS w__29) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__31 ← (( do
    if (((BEq.beq walkparams.tgx TGx_4KB) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__31 : Bool)
    then
      (do
        let w__32 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let w__33 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with sl2 := ((_get_VTCR_EL2_Type_SL2 w__32) &&& (_get_VTCR_EL2_Type_DS w__33)) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with sl2 := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__36 ← (( do
    if ((← do
         (HaveFeatCMOW ())) : Bool)
    then
      (do
        (IsHCRXEL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__38 ← (( do
    if (w__36 : Bool)
    then
      (do
        let w__37 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCRX_EL2_Type_CMOW w__37))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__38 } : S2TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S2TTWParams := { walkparams with s2pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__39 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
        let w__41 ← (( do
          if (w__39 : Bool)
          then
            (do
              let w__40 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VTCR_EL2_Type_S2PIE w__40))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with s2pie := w__41 } : S2TTWParams)
        (pure (walkparams))) ) : SailM S2TTWParams )
  let w__42 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
  let w__44 ← (( do
    if (w__42 : Bool)
    then
      (do
        let w__43 ← (( do readReg S2PIR_EL2 ) : SailM (BitVec 64) )
        (pure ((Mk_S2PIRType w__43))))
    else (pure ((Mk_S2PIRType (Zeros (n := 64))))) ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with s2pir := w__44 } : S2TTWParams)
  let w__46 ← (( do
    (pure ((← do
          (HaveTHExt ())) && ((walkparams.d128 != 1#1) : Bool))) ) : SailM Bool )
  let walkparams ← (( do
    if (w__46 : Bool)
    then
      (do
        let w__47 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with assuredonly := (_get_VTCR_EL2_Type_AssuredOnly w__47) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with assuredonly := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__48 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__50 ← (( do
    if (w__48 : Bool)
    then
      (do
        let w__49 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL0 w__49))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl0 := w__50 } : S2TTWParams)
  let w__51 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__53 ← (( do
    if (w__51 : Bool)
    then
      (do
        let w__52 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL1 w__52))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl1 := w__53 } : S2TTWParams)
  let w__55 ← (( do
    (pure ((← do
          (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool))) ) : SailM Bool
    )
  if (w__55 : Bool)
  then
    (do
      let w__56 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
      let walkparams := ({ walkparams with haft := (_get_VTCR_EL2_Type_HAFT w__56) } : S2TTWParams)
      (pure (walkparams)))
  else
    (let walkparams : S2TTWParams := { walkparams with haft := 0#1 }
    (pure (walkparams)))


end ArmFull.Functions
