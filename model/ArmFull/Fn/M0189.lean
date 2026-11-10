import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0014
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0098
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186

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

/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_SS2TTWParams (ipaspace : PASpace) (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 1507) ()) ) : SailM S2TTWParams )
  let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  let w__2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_D128 w__1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with d128 := w__2 } : S2TTWParams)
  let walkparams ← (( do
    if ((BEq.beq ipaspace PAS_Secure) : Bool)
    then
      (do
        let w__3 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
        let w__4 ← (( do (AArch64_S2DecodeTG0 (_get_VSTCR_EL2_Type_TG0 w__3)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__4 } : S2TTWParams)
        let w__5 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with txsz := (_get_VSTCR_EL2_Type_T0SZ w__5) } : S2TTWParams)
        let walkparams ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__6 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
              let walkparams :=
                ({ walkparams with skl := (_get_VSTTBR_EL2_Type_SKL w__6) } : S2TTWParams)
              (pure (walkparams)))
          else
            (do
              let w__7 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
              let walkparams :=
                ({ walkparams with sl0 := (_get_VSTCR_EL2_Type_SL0 w__7) } : S2TTWParams)
              (pure (walkparams))) ) : SailM S2TTWParams )
        let w__9 ← (( do
          if (((BEq.beq walkparams.tgx TGx_4KB) : Bool) : Bool)
          then
            (do
              (Have52BitIPAAndPASpaceExt ()))
          else (pure false) ) : SailM Bool )
        if (w__9 : Bool)
        then
          (do
            let w__10 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
            let w__11 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            let walkparams :=
              ({ walkparams with sl2 := ((_get_VSTCR_EL2_Type_SL2 w__10) &&& (_get_VTCR_EL2_Type_DS
                    w__11)) } : S2TTWParams)
            (pure (walkparams)))
        else
          (let walkparams : S2TTWParams := { walkparams with sl2 := 0#1 }
          (pure (walkparams))))
    else
      (do
        if ((BEq.beq ipaspace PAS_NonSecure) : Bool)
        then
          (do
            let w__12 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            let w__13 ← (( do (AArch64_S2DecodeTG0 (_get_VTCR_EL2_Type_TG0 w__12)) ) : SailM TGx )
            let walkparams := ({ walkparams with tgx := w__13 } : S2TTWParams)
            let w__14 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            let walkparams :=
              ({ walkparams with txsz := (_get_VTCR_EL2_Type_T0SZ w__14) } : S2TTWParams)
            let walkparams ← (( do
              if ((walkparams.d128 == 1#1) : Bool)
              then
                (do
                  let w__15 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                  let walkparams :=
                    ({ walkparams with skl := (_get_VTTBR_EL2_Type_SKL w__15) } : S2TTWParams)
                  (pure (walkparams)))
              else
                (do
                  let w__16 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                  let walkparams :=
                    ({ walkparams with sl0 := (_get_VTCR_EL2_Type_SL0 w__16) } : S2TTWParams)
                  (pure (walkparams))) ) : SailM S2TTWParams )
            let w__18 ← (( do
              if (((BEq.beq walkparams.tgx TGx_4KB) : Bool) : Bool)
              then
                (do
                  (Have52BitIPAAndPASpaceExt ()))
              else (pure false) ) : SailM Bool )
            if (w__18 : Bool)
            then
              (do
                let w__19 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                let w__20 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                let walkparams :=
                  ({ walkparams with sl2 := ((_get_VTCR_EL2_Type_SL2 w__19) &&& (_get_VTCR_EL2_Type_DS
                        w__20)) } : S2TTWParams)
                (pure (walkparams)))
            else
              (let walkparams : S2TTWParams := { walkparams with sl2 := 0#1 }
              (pure (walkparams))))
        else
          (do
            (Unreachable ())
            (pure (walkparams)))) ) : SailM S2TTWParams )
  let w__21 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sw := (_get_VSTCR_EL2_Type_SW w__21) } : S2TTWParams)
  let w__22 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with nsw := (_get_VTCR_EL2_Type_NSW w__22) } : S2TTWParams)
  let w__23 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sa := (_get_VSTCR_EL2_Type_SA w__23) } : S2TTWParams)
  let w__24 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with nsa := (_get_VTCR_EL2_Type_NSA w__24) } : S2TTWParams)
  let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let walkparams :=
    ({ walkparams with vm := ((_get_HCR_EL2_Type_VM w__25) ||| (_get_HCR_EL2_Type_DC w__26)) } : S2TTWParams)
  let w__27 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_VTCR_EL2_Type_PS w__27) } : S2TTWParams)
  let w__28 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_VTCR_EL2_Type_IRGN0 w__28) } : S2TTWParams)
  let w__29 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_VTCR_EL2_Type_ORGN0 w__29) } : S2TTWParams)
  let w__30 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_VTCR_EL2_Type_SH0 w__30) } : S2TTWParams)
  let w__31 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__31) } : S2TTWParams)
  let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__34 ← (( do
    if (((_get_HCR_EL2_Type_TGE w__32) == 0#1) : Bool)
    then
      (do
        let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_PTW w__33))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ptw := w__34 } : S2TTWParams)
  let w__35 ← (( do (HaveStage2MemAttrControl ()) ) : SailM Bool )
  let w__37 ← (( do
    if (w__35 : Bool)
    then
      (do
        let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_FWB w__36))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with fwb := w__37 } : S2TTWParams)
  let w__38 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__40 ← (( do
    if (w__38 : Bool)
    then
      (do
        let w__39 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HA w__39))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__40 } : S2TTWParams)
  let w__41 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__43 ← (( do
    if (w__41 : Bool)
    then
      (do
        let w__42 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HD w__42))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__43 } : S2TTWParams)
  let w__45 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__45 : Bool)
    then
      (do
        let w__46 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_VTCR_EL2_Type_DS w__46) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__49 ← (( do
    if ((← do
         (HaveFeatCMOW ())) : Bool)
    then
      (do
        (IsHCRXEL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__51 ← (( do
    if (w__49 : Bool)
    then
      (do
        let w__50 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCRX_EL2_Type_CMOW w__50))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__51 } : S2TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S2TTWParams := { walkparams with s2pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__52 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
        let w__54 ← (( do
          if (w__52 : Bool)
          then
            (do
              let w__53 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VTCR_EL2_Type_S2PIE w__53))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with s2pie := w__54 } : S2TTWParams)
        (pure (walkparams))) ) : SailM S2TTWParams )
  let w__55 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
  let w__57 ← (( do
    if (w__55 : Bool)
    then
      (do
        let w__56 ← (( do readReg S2PIR_EL2 ) : SailM (BitVec 64) )
        (pure ((Mk_S2PIRType w__56))))
    else (pure ((Mk_S2PIRType (Zeros (n := 64))))) ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with s2pir := w__57 } : S2TTWParams)
  let w__59 ← (( do
    (pure ((← do
          (HaveTHExt ())) && ((walkparams.d128 != 1#1) : Bool))) ) : SailM Bool )
  let walkparams ← (( do
    if (w__59 : Bool)
    then
      (do
        let w__60 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with assuredonly := (_get_VTCR_EL2_Type_AssuredOnly w__60) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with assuredonly := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__61 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__63 ← (( do
    if (w__61 : Bool)
    then
      (do
        let w__62 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL0 w__62))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl0 := w__63 } : S2TTWParams)
  let w__64 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__66 ← (( do
    if (w__64 : Bool)
    then
      (do
        let w__65 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL1 w__65))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl1 := w__66 } : S2TTWParams)
  let w__68 ← (( do
    (pure ((← do
          (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool))) ) : SailM Bool
    )
  let walkparams ← (( do
    if (w__68 : Bool)
    then
      (do
        let w__69 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_VTCR_EL2_Type_HAFT w__69) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let walkparams : S2TTWParams := { walkparams with emec := 0#1 }
  (pure (walkparams))


def AArch64_GetS2TLBContext (ss : SecurityState) (ipa : FullAddress) (tg : TGx) : SailM TLBContext := do
  let w__0 ← (( do (EL2Enabled ()) ) : SailM Bool )
  ArmFull.assert w__0 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26612.23-26612.24"
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1551) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL10 }
  let tlbcontext : TLBContext := { tlbcontext with ipaspace := ipa.paspace }
  let w__1 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
  let tlbcontext := ({ tlbcontext with vmid := w__1 } : TLBContext)
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend ipa.address 64) }
  let w__2 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let tlbcontext ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__5 ← (( do
          if ((BEq.beq ipa.paspace PAS_Secure) : Bool)
          then
            (do
              let w__3 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VSTTBR_EL2_Type_CnP w__3))))
          else
            (do
              let w__4 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_VTTBR_EL2_Type_CnP w__4)))) ) : SailM (BitVec 1) )
        let tlbcontext := ({ tlbcontext with cnp := w__5 } : TLBContext)
        (pure (tlbcontext)))
    else
      (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
      (pure (tlbcontext))) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with includes_s1_name := false }
  let tlbcontext : TLBContext := { tlbcontext with includes_s2_name := true }
  let tlbcontext : TLBContext := { tlbcontext with includes_gpt_name := false }
  (pure (tlbcontext))


def MismatchedCpySetTargetEL (_ : Unit) : SailM (BitVec 2) := do
  let target_el ← (( do (undefined_bitvector_at (← occLabel 1763) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__0.EL) >b (BitVec.toNat EL1)) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let target_el := (w__1.EL : (BitVec 2))
      (pure (target_el)))
  else
    (do
      let w__6 ← (( do
        if ((← do
             if ((← do
                  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__2.EL == EL0) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__5) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
      then (pure (EL2))
      else
        (do
          let w__13 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__7.EL == EL1) : Bool)))) : Bool)
                      then
                        (do
                          (EL2Enabled ()))
                      else (pure false)) : Bool)
                 then
                   (do
                     (IsHCRXEL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__12 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCRX_EL2_Type_MCE2 w__12) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          let target_el : (BitVec 2) :=
            if (w__13 : Bool)
            then EL2
            else EL1
          (pure (target_el))))


def ExternalDebugInterruptsDisabled (target : (BitVec 2)) : SailM Bool := do
  let int_dis ← (( do (undefined_bool_at (← occLabel 1929) ()) ) : SailM Bool )
  let ss ← (( do (SecurityStateAtEL target) ) : SailM SecurityState )
  let w__0 ← (( do (Havev8p4Debug ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (_get_EDSCR_Type_INTdis w__1) 0)])) == 1#1) : Bool)
      then
        (do
          match ss with
          | .SS_NonSecure =>
            (do
              (ExternalInvasiveDebugEnabled ()))
          | .SS_Secure =>
            (do
              (ExternalSecureInvasiveDebugEnabled ()))
          | .SS_Realm =>
            (do
              (ExternalRealmInvasiveDebugEnabled ()))
          | .SS_Root =>
            (do
              (ExternalRootInvasiveDebugEnabled ())))
      else (pure (false)))
  else
    (do
      let questionMark := target
      if ((questionMark == EL3) : Bool)
      then
        (do
          if ((← do
               let w__6 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
               (pure ((((_get_EDSCR_Type_INTdis w__6) == 0b11#2) : Bool)))) : Bool)
          then
            (do
              (ExternalSecureInvasiveDebugEnabled ()))
          else (pure false))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              if ((← do
                   let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                   let b__0 := (_get_EDSCR_Type_INTdis w__9)
                   (pure ((if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (1#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)))) : Bool)
              then
                (do
                  (ExternalInvasiveDebugEnabled ()))
              else (pure false))
          else
            (do
              if ((questionMark == EL1) : Bool)
              then
                (do
                  if ((BEq.beq ss SS_Secure) : Bool)
                  then
                    (do
                      if ((← do
                           let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           let b__1 := (_get_EDSCR_Type_INTdis w__12)
                           (pure ((if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1
                                    1 1)) == (1#1 : (BitVec 1))) : Bool)
                             then true
                             else false : Bool)))) : Bool)
                      then
                        (do
                          (ExternalSecureInvasiveDebugEnabled ()))
                      else (pure false))
                  else
                    (do
                      if ((← do
                           let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_INTdis w__15) != 0b00#2) : Bool)))) : Bool)
                      then
                        (do
                          (ExternalInvasiveDebugEnabled ()))
                      else (pure false)))
              else (pure (int_dis)))))


def AArch64_ClearEventCounters (_ : Unit) : SailM Unit := do
  let counters ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM Int )
  if ((counters != 0) : Bool)
  then
    (do
      let loop_idx_lower : Nat := 0
      let loop_idx_upper : Int := (counters -i 1)
      (do
        let mut loop_vars := ()
        for idx in [loop_idx_lower:loop_idx_upper:1]i do
          let () := loop_vars
          loop_vars ← do
            ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34397.64-34397.65"
            let w__0 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
            writeReg PMEVCNTR_EL0 (vectorUpdate w__0 (Sail.Int.toNatChecked (idx)) (Zeros (n := 64)))
        (pure loop_vars)))
  else (pure (()))


def AArch64_PMUSwIncrement (sw_incr : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
         (pure ((((_get_PMCR_EL0_Type_E w__0) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_MDCR_EL2_Type_HPME w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (()))
  else
    (do
      let counters ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34413.64-34413.65"
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access sw_incr
                         (Sail.Int.toNatChecked (idx)))])) == 1#1) : Bool)
                then
                  (do
                    (PMUEvent__2 PMU_EVENT_SW_INCR 1 idx))
                else (pure (()))
            (pure loop_vars)))
      else (pure (())))


def AArch32_WriteModeByInstr (mode : (BitVec 5)) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2766) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 2767) ()) ) : SailM Bool )
  let w__0 ← (( do (ELFromM32 mode) ) : SailM (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let valid_name : Bool := tup__0
  let el : (BitVec 2) := tup__1
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let valid_name : Bool :=
    if (((BitVec.toNat el) >b (BitVec.toNat w__1.EL)) : Bool)
    then false
    else valid_name
  let w__5 ← (( do
    if ((← do
         (pure ((← do
               let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__2.M == M32_Hyp) : Bool)))) || ((mode == M32_Hyp) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__4.M != mode) : Bool))))
    else (pure false) ) : SailM Bool )
  let valid_name : Bool :=
    if (w__5 : Bool)
    then false
    else valid_name
  let w__12 ← (( do
    if ((← do
         if ((← do
              (pure ((← do
                    (pure ((← do
                          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__6.M == M32_Monitor) : Bool)))) && ((HaveEL EL2) : Bool)))) && ((el == EL1) : Bool)))) : Bool)
         then
           (do
             let w__9 ← (( do readReg SCR ) : SailM (BitVec 32) )
             (pure ((((_get_SCR_Type_NS w__9) == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__11 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HCR_Type_TGE w__11) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let valid_name : Bool :=
    if (w__12 : Bool)
    then false
    else valid_name
  let valid_name := valid_name
  if ((! valid_name) : Bool)
  then
    (do
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__13 with IL := 1#1 })
  else
    (do
      (AArch32_WriteMode mode))


/-- Type quantifiers: idx : Nat, increment_name : Int, 0 ≤ idx ∧ idx < 31 -/
def AArch32_IncrementEventCounter (idx : Nat) (increment_name : Int) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (0 ≤b idx) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:43482.36-43482.37"
      ArmFull.assert (idx <b 31) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:43483.36-43483.37"
      (AArch64_IncrementEventCounter idx increment_name))
  else
    (do
      let w__1 ← (( do (PMEVCNTR_read idx) ) : SailM (BitVec 32) )
      let old_value : Int := (BitVec.toNat w__1)
      let w__2 ← (( do (PMUCountValue idx increment_name) ) : SailM Int )
      let new_value : Int := (old_value +i w__2)
      (PMEVCNTR_set idx (integer_subrange new_value 31 0))
      let ovflw : Nat := 32
      if (((Sail.BitVec.castWidth (m := (64 - (Sail.Int.toNatChecked ovflw) + 1)) (integer_subrange
             old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
      then
        (do
          let w__3 ← (( do (PMOVSSET_read ()) ) : SailM (BitVec 32) )
          (PMOVSSET_write
            (Mk_PMOVSSET_Type (Sail.BitVec.updateSubrange w__3 idx idx (Sail.BitVec.castWidth 1#1))))
          let w__4 ← (( do (PMOVSR_read ()) ) : SailM (BitVec 32) )
          (PMOVSR_write
            (Mk_PMOVSR_Type (Sail.BitVec.updateSubrange w__4 idx idx (Sail.BitVec.castWidth 1#1))))
          let w__6 ← (( do
            if ((((BitVec.setWidth 1 (BitVec.join1 [(integer_access idx 0)])) == 0#1) : Bool) : Bool)
            then
              (do
                let w__5 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                (pure ((((idx +i 1) <b w__5) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (PMUEvent__2 PMU_EVENT_CHAIN 1 (idx +i 1)))
          else (pure (())))
      else (pure (())))


def AArch32_PMUSwIncrement (sw_incr : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_PMCR_Type_E w__0) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HDCR_Type_HPME w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (()))
  else
    (do
      let counters ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:43529.64-43529.65"
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access sw_incr
                         (Sail.Int.toNatChecked (idx)))])) == 1#1) : Bool)
                then
                  (do
                    (PMUEvent__2 PMU_EVENT_SW_INCR 1 idx))
                else (pure (()))
            (pure loop_vars)))
      else (pure (())))


end ArmFull.Functions
