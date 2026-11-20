module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0012
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184 set_option backward.proofsInPublic true @[expose] public section

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

def IsSCTLR2EL1Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatSCTLR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_SCTLR2En w__2) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (false))
      else
        (do
          let w__8 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                if ((← do
                     let w__5 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                     (pure (((! w__5) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCRX_EL2_Type_SCTLR2En w__6) == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          let w__9 : Bool :=
            if (w__8 : Bool)
            then false
            else true
          (pure (w__9))))


def SecurityStateForRegime (regime : Regime) : SailM SecurityState := do
  match regime with
  | .Regime_EL3 =>
    (do
      (SecurityStateAtEL EL3))
  | .Regime_EL30 => (pure (SS_Secure))
  | .Regime_EL2 =>
    (do
      (SecurityStateAtEL EL2))
  | .Regime_EL20 =>
    (do
      (SecurityStateAtEL EL2))
  | .Regime_EL10 =>
    (do
      (SecurityStateAtEL EL1))


def IsTCR2EL1Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatTCR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_TCR2En w__2) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (false))
      else
        (do
          let w__8 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                if ((← do
                     let w__5 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                     (pure (((! w__5) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCRX_EL2_Type_TCR2En w__6) == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          let w__9 : Bool :=
            if (w__8 : Bool)
            then false
            else true
          (pure (w__9))))


def AArch64_S1TTWParamsEL2 (ss : SecurityState) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1265) ()) ) : SailM S1TTWParams )
  let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let w__1 ← (( do (AArch64_S1DecodeTG0 (_get_TCR_EL2_Type_TG0 w__0)) ) : SailM TGx )
  let walkparams := ({ walkparams with tgx := w__1 } : S1TTWParams)
  let w__2 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with txsz := (_get_TCR_EL2_Type_T0SZ w__2) } : S1TTWParams)
  let w__3 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL2_Type_PS w__3) } : S1TTWParams)
  let w__4 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_TCR_EL2_Type_IRGN0 w__4) } : S1TTWParams)
  let w__5 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_TCR_EL2_Type_ORGN0 w__5) } : S1TTWParams)
  let w__6 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_TCR_EL2_Type_SH0 w__6) } : S1TTWParams)
  let w__7 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with tbi := (_get_TCR_EL2_Type_TBI w__7) } : S1TTWParams)
  let w__8 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__8) } : S1TTWParams)
  let w__9 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do readReg MAIR2_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__10) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__13 ← (( do
    if ((← do
         (HaveAIEExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__15 ← (( do
    if (w__13 : Bool)
    then
      (do
        let w__14 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_AIE w__14))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__15 } : S1TTWParams)
  let w__16 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL2_Type_WXN w__16) } : S1TTWParams)
  let w__17 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__17) } : S1TTWParams)
  let w__22 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        if ((← do
             let w__19 ← (( do (HaveRME ()) ) : SailM Bool )
             (pure (((! w__19) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (HaveSecureEL2Ext ())))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__22 : Bool)
    then
      (do
        let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sif := (_get_SCR_EL3_Type_SIF w__23) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with sif := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__24 ← (( do (HavePACExt ()) ) : SailM Bool )
  let w__26 ← (( do
    if (w__24 : Bool)
    then
      (do
        let w__25 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL2_Type_TBID w__25))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tbid := w__26 } : S1TTWParams)
  let w__27 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
  let w__29 ← (( do
    if (w__27 : Bool)
    then
      (do
        let w__28 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL2_Type_HPD w__28))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hpd := w__29 } : S1TTWParams)
  let w__30 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__34 ← (( do
    if (w__30 : Bool)
    then
      (do
        let w__31 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__33 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__32) == 0#1) : Bool)
          then 21
          else 39
        (pure ((BitVec.slice w__31 (Sail.Int.toNatChecked (w__33)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__34 } : S1TTWParams)
  let w__35 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__39 ← (( do
    if (w__35 : Bool)
    then
      (do
        let w__36 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__38 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__37) == 0#1) : Bool)
          then 22
          else 40
        (pure ((BitVec.slice w__36 (Sail.Int.toNatChecked (w__38)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__39 } : S1TTWParams)
  let w__41 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__41 : Bool)
    then
      (do
        let w__42 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__44 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__43) == 0#1) : Bool)
          then 32
          else 59
        let walkparams :=
          ({ walkparams with ds := (BitVec.slice w__42 (Sail.Int.toNatChecked (w__44)) 1) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__47 ← (( do
    if ((← do
         (HaveS1PIExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__49 ← (( do
    if (w__47 : Bool)
    then
      (do
        let w__48 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_PIE w__48))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with pie := w__49 } : S1TTWParams)
  let w__50 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__50 : Bool)
    then
      (do
        let w__51 ← (( do readReg PIR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__51) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__52 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
  let w__54 ← (( do
    if (w__52 : Bool)
    then
      (do
        let w__53 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL2_Type_MTX w__53))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with mtx := w__54 } : S1TTWParams)
  let w__57 ← (( do
    if ((← do
         (HaveTHExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__59 ← (( do
    if (w__57 : Bool)
    then
      (do
        let w__58 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_PnCH w__58))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with pnch := w__59 } : S1TTWParams)
  let w__63 ← (( do
    if ((← do
         (pure ((← do
               (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__63 : Bool)
    then
      (do
        let w__64 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_TCR2_EL2_Type_HAFT w__64) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__67 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__69 ← (( do
    if (w__67 : Bool)
    then
      (do
        let w__68 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__68))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__69 } : S1TTWParams)
  let w__73 ← (( do
    if ((← do
         (pure ((← do
               (HaveFeatMEC ())) && ((BEq.beq ss SS_Realm) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__73 : Bool)
  then
    (do
      let w__74 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let walkparams := ({ walkparams with amec := (_get_TCR2_EL2_Type_AMEC0 w__74) } : S1TTWParams)
      (pure (walkparams)))
  else
    (let walkparams : S1TTWParams := { walkparams with amec := 0#1 }
    (pure (walkparams)))


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
  let w__75 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        if ((← do
             let w__72 ← (( do (HaveRME ()) ) : SailM Bool )
             (pure (((! w__72) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (HaveSecureEL2Ext ())))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__75 : Bool)
    then
      (do
        let w__76 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sif := (_get_SCR_EL3_Type_SIF w__76) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with sif := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__77 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__77 : Bool)
    then
      (do
        let w__78 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with ntlsmd := (_get_SCTLR_EL2_Type_nTLSMD w__78) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ntlsmd := 1#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__79 ← (( do (HaveFeatCMOW ()) ) : SailM Bool )
  let w__81 ← (( do
    if (w__79 : Bool)
    then
      (do
        let w__80 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR_EL2_Type_CMOW w__80))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__81 } : S1TTWParams)
  let w__82 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__86 ← (( do
    if (w__82 : Bool)
    then
      (do
        let w__83 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__84 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__85 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__84) == 0#1) : Bool)
          then 21
          else 39
        (pure ((BitVec.slice w__83 (Sail.Int.toNatChecked (w__85)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__86 } : S1TTWParams)
  let w__87 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__91 ← (( do
    if (w__87 : Bool)
    then
      (do
        let w__88 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__89 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__90 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__89) == 0#1) : Bool)
          then 22
          else 40
        (pure ((BitVec.slice w__88 (Sail.Int.toNatChecked (w__90)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__91 } : S1TTWParams)
  let w__93 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__93 : Bool)
    then
      (do
        let w__94 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__95 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__96 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__95) == 0#1) : Bool)
          then 32
          else 59
        let walkparams :=
          ({ walkparams with ds := (BitVec.slice w__94 (Sail.Int.toNatChecked (w__96)) 1) } : S1TTWParams)
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
        let w__99 ← (( do
          if ((← do
               (HaveS1PIExt ())) : Bool)
          then
            (do
              (IsTCR2EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        let w__101 ← (( do
          if (w__99 : Bool)
          then
            (do
              let w__100 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL2_Type_PIE w__100))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with pie := w__101 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__102 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__102 : Bool)
    then
      (do
        let w__103 ← (( do readReg PIR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__103) } : S1TTWParams)
        let w__104 ← (( do readReg PIRE0_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pire0 := (Mk_S1PIRType w__104) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__105 ← (( do (HavePAN3Ext ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__105 : Bool)
    then
      (do
        let w__107 ← (( do
          if ((walkparams.pie == 0#1) : Bool)
          then
            (do
              let w__106 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EPAN w__106))))
          else (pure (1#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with epan := w__107 } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with epan := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__111 ← (( do
    if ((← do
         (pure ((← do
               (HaveTHExt ())) && ((walkparams.d128 == 0#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__111 : Bool)
    then
      (do
        let w__112 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with pnch := (_get_TCR2_EL2_Type_PnCH w__112) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with pnch := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__116 ← (( do
    if ((← do
         (pure ((← do
               (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__116 : Bool)
    then
      (do
        let w__117 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_TCR2_EL2_Type_HAFT w__117) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__120 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__122 ← (( do
    if (w__120 : Bool)
    then
      (do
        let w__121 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__121))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__122 } : S1TTWParams)
  let w__126 ← (( do
    if ((← do
         (pure ((← do
               (HaveFeatMEC ())) && ((BEq.beq ss SS_Realm) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__126 : Bool)
  then
    (do
      let w__129 ← (( do
        if ((BEq.beq varange VARange_LOWER) : Bool)
        then
          (do
            let w__127 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_TCR2_EL2_Type_AMEC0 w__127))))
        else
          (do
            let w__128 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_TCR2_EL2_Type_AMEC1 w__128)))) ) : SailM (BitVec 1) )
      let walkparams := ({ walkparams with amec := w__129 } : S1TTWParams)
      (pure (walkparams)))
  else
    (let walkparams : S1TTWParams := { walkparams with amec := 0#1 }
    (pure (walkparams)))


end ArmFull.Functions
