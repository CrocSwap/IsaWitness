import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0048
import ArmFull.Fn.M0051
import ArmFull.Fn.M0056
import ArmFull.Fn.M0058
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0115
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0197
import ArmFull.Fn.M0198
import ArmFull.Fn.M0200
import ArmFull.Fn.M0209
import ArmFull.Fn.M0213
import ArmFull.Fn.M0219
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0238
import ArmFull.Fn.M0246
import ArmFull.Fn.M0249
import ArmFull.Fn.M0252
import ArmFull.Fn.M0253
import ArmFull.Fn.M0255
import ArmFull.Fn.M0259
import ArmFull.Fn.M0580
import ArmFull.Fn.M0581
import ArmFull.Fn.M0840
import ArmFull.Fn.M0841

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

/-- Type quantifiers: N : Int -/
def FPProcessDenorms (type1 : FPType) (type2 : FPType) (N : Int) (fpcr : (BitVec 64)) : SailM Unit := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  if (((altfp && (N != 16)) && ((BEq.beq type1 FPType_Denormal) || (BEq.beq type2 FPType_Denormal))) : Bool)
  then
    (do
      (FPProcessException FPExc_InputDenorm fpcr))
  else (pure (()))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaN__1 (fptype : FPType) (op : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16162.41-16162.42"
  ArmFull.assert ((BEq.beq fptype FPType_QNaN) || (BEq.beq fptype FPType_SNaN)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16163.56-16163.57"
  let topfrac : Int := 9
  let topfrac : Int :=
    match (Sail.BitVec.length op) with
    | 16 => 9
    | 32 => 22
    | 64 => 51
    | _ => topfrac
  let topfrac : Int := topfrac
  let result : (BitVec k_N) := op
  let result ← (( do
    if ((BEq.beq fptype FPType_SNaN) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b topfrac) && (topfrac <b (Sail.BitVec.length result))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16180.58-16180.59"
        let result : (BitVec k_N) :=
          (BitVec.update result (Sail.Int.toNatChecked (topfrac)) (Bit 1#1))
        if (fpexc : Bool)
        then
          (do
            (FPProcessException FPExc_InvalidOp fpcr))
        else (pure (()))
        (pure (result)))
    else (pure (result)) ) : SailM (BitVec k_N) )
  if (((_get_FPCRType_DN fpcr) == 1#1) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))))
  else (pure (result))


/-- Type quantifiers: N : Int -/
def FPProcessDenorm (fptype : FPType) (N : Int) (fpcr : (BitVec 64)) : SailM Unit := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  if (((altfp && (N != 16)) && (BEq.beq fptype FPType_Denormal)) : Bool)
  then
    (do
      (FPProcessException FPExc_InputDenorm fpcr))
  else (pure (()))


/-- Type quantifiers: N : Int -/
def FPProcessDenorms3 (type1 : FPType) (type2 : FPType) (type3 : FPType) (N : Int) (fpcr : (BitVec 64)) : SailM Unit := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  if (((altfp && (N != 16)) && (((BEq.beq type1 FPType_Denormal) || (BEq.beq type2 FPType_Denormal)) || (BEq.beq
           type3 FPType_Denormal))) : Bool)
  then
    (do
      (FPProcessException FPExc_InputDenorm fpcr))
  else (pure (()))


/-- Type quantifiers: k_aligned : Bool, size : Int -/
def AArch64_TranslateAddress (va : (BitVec 64)) (accdesc : AccessDescriptor) (aligned : Bool) (size : Int) : SailM AddressDescriptor := do
  let w__1 ← (( do
    (pure ((← do
          readReg SPESampleInFlight) && ((! ((BEq.beq accdesc.acctype AccessType_IFETCH) || (BEq.beq
              accdesc.acctype AccessType_SPE))) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      (SPEStartCounter SPECounterPosTranslationLatency))
  else (pure (()))
  let regime ← (( do (TranslationRegime accdesc.el) ) : SailM Regime )
  let tsi ← (( do (AArch64_GetTranslationStartInfo regime accdesc.ss accdesc va size) ) : SailM
    TranslationStartInfo )
  (start_translation tsi)
  let result ← (( do (AArch64_FullTranslate va accdesc aligned) ) : SailM AddressDescriptor )
  let result ← (( do
    if (((! (IsFault result)) && (bne accdesc.acctype AccessType_IFETCH)) : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_CheckDebug va accdesc size) ) : SailM FaultRecord )
        let result := ({ result with fault := w__2 } : AddressDescriptor)
        (pure (result)))
    else (pure (result)) ) : SailM AddressDescriptor )
  let w__7 ← (( do
    if ((← do
         (pure ((← do
               (HaveRME ())) && ((! (IsFault result)) : Bool)))) : Bool)
    then
      (do
        if (((bne accdesc.acctype AccessType_DC) : Bool) : Bool)
        then (pure true)
        else
          (do
            (__IMPDEF_boolean "GPC Fault on DC operations")))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (w__7 : Bool)
    then
      (do
        let w__8 ← (( do (GranuleProtectionCheck result accdesc) ) : SailM GPCFRecord )
        let result :=
          ({ result with fault := { result.fault with gpcf := w__8 } } : AddressDescriptor)
        let result : AddressDescriptor :=
          if ((bne result.fault.gpcf.gpf GPCF_None) : Bool)
          then
            (let result : AddressDescriptor :=
              { result with fault := { result.fault with statuscode := Fault_GPCFOnOutput } }
            { result with fault := { result.fault with paddress := result.paddress } })
          else result
        (pure (result)))
    else (pure (result)) ) : SailM AddressDescriptor )
  let result ← (( do
    if (((! (IsFault result)) && (BEq.beq accdesc.acctype AccessType_IFETCH)) : Bool)
    then
      (do
        let w__9 ← (( do (AArch64_CheckDebug va accdesc size) ) : SailM FaultRecord )
        let result := ({ result with fault := w__9 } : AddressDescriptor)
        (pure (result)))
    else (pure (result)) ) : SailM AddressDescriptor )
  let w__11 ← (( do
    (pure ((← do
          readReg SPESampleInFlight) && ((! ((BEq.beq accdesc.acctype AccessType_IFETCH) || (BEq.beq
              accdesc.acctype AccessType_SPE))) : Bool))) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      (SPEStopCounter SPECounterPosTranslationLatency))
  else (pure (()))
  let result : AddressDescriptor := { result with vaddress := (Sail.BitVec.zeroExtend va 64) }
  (end_translation result)
  (pure (result))


def CheckNonStreamingSVEEnabled (_ : Unit) : SailM Unit := do
  (CheckSVEEnabled ())
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveSME ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.SM == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (IsFullA64Enabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      (SMEAccessTrap SMEExceptionType_Streaming w__5.EL))
  else (pure (()))


def CheckFPAdvSIMDEnabled64 (_ : Unit) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())


def AArch64_AT (address : (BitVec 64)) (stage_in : TranslationStage) (el_in : (BitVec 2)) (ataccess : ATAccess) : SailM Unit := do
  let stage : TranslationStage := stage_in
  let el : (BitVec 2) := el_in
  let w__0 ← (( do (EffectiveSCR_EL3_NSE ()) ) : SailM (BitVec 1) )
  let w__1 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
  let effective_nse_ns : (BitVec 2) := (w__0 +++ w__1)
  let w__6 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     (HaveRME ())) : Bool)
                then
                  (do
                    let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__3.EL == EL3) : Bool))))
                else (pure false)) && ((effective_nse_ns == 0b10#2) : Bool)))) && ((el != EL3) : Bool)))
    ) : SailM Bool )
  if (w__6 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__10 ← (( do
    (pure ((← do
          (pure ((← do
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) == 0b11#2) : Bool)))) && ((el == EL1) : Bool)))) && ((BEq.beq
          stage TranslationStage_1) : Bool))) ) : SailM Bool )
  let el : (BitVec 2) :=
    if (w__10 : Bool)
    then EL2
    else el
  let w__12 ← (( do
    if ((((HaveEL EL3) && (BEq.beq stage TranslationStage_12)) : Bool) : Bool)
    then
      (do
        let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
        (pure (((! w__11) : Bool))))
    else (pure false) ) : SailM Bool )
  let stage : TranslationStage :=
    if (w__12 : Bool)
    then TranslationStage_1
    else stage
  let write : Bool := ((BEq.beq ataccess ATAccess_WritePAN) || (BEq.beq ataccess ATAccess_Write))
  let ss ← (( do (SecurityStateAtEL el) ) : SailM SecurityState )
  let pan : Bool := ((BEq.beq ataccess ATAccess_ReadPAN) || (BEq.beq ataccess ATAccess_WritePAN))
  let accdesc ← (( do (CreateAccDescAT ss el write pan) ) : SailM AccessDescriptor )
  let aligned : Bool := true
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let regime ← (( do (undefined_Regime (← occLabel 2639) ()) ) : SailM Regime )
  let regime ← (( do
    if ((BEq.beq stage TranslationStage_12) : Bool)
    then (pure (Regime_EL10))
    else
      (do
        (TranslationRegime el)) ) : SailM Regime )
  let addrdesc ← (( do (undefined_AddressDescriptor (← occLabel 2640) ()) ) : SailM
    AddressDescriptor )
  let w__18 ← (( do
    if ((← do
         if (((el == EL0) : Bool) : Bool)
         then
           (do
             (ELUsingAArch32 EL1))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if (((el != EL0) : Bool) : Bool)
        then
          (do
            (ELUsingAArch32 el))
        else (pure false)) ) : SailM Bool )
  let (addrdesc, fault) ← (( do
    if (w__18 : Bool)
    then
      (do
        let tsi ← (( do
          (AArch32_GetTranslationStartInfo regime ss accdesc (Sail.BitVec.extractLsb address 31 0) 1)
          ) : SailM TranslationStartInfo )
        (start_translation tsi)
        let w__20 ← (( do
          if (((BEq.beq regime Regime_EL2) : Bool) : Bool)
          then (pure true)
          else
            (do
              let w__19 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
              (pure ((((_get_TTBCR_Type_EAE w__19) == 1#1) : Bool)))) ) : SailM Bool )
        if (w__20 : Bool)
        then
          (do
            let w__21 ← (( do
              (AArch32_S1TranslateLD fault regime (Sail.BitVec.extractLsb address 31 0) aligned
                accdesc) ) : SailM (FaultRecord × AddressDescriptor) )
            let (tup__0, tup__1) := (w__21 : (FaultRecord × AddressDescriptor))
            let fault : FaultRecord := tup__0
            let addrdesc : AddressDescriptor := tup__1
            (pure ((addrdesc, fault))))
        else
          (do
            let (__tup_0, __tup_1, _) ← (( do
              (AArch32_S1TranslateSD fault regime (Sail.BitVec.extractLsb address 31 0) aligned
                accdesc) ) : SailM (FaultRecord × AddressDescriptor × SDFType) )
            let fault : FaultRecord := __tup_0
            let addrdesc : AddressDescriptor := __tup_1
            (pure ((addrdesc, fault)))))
    else
      (do
        let tsi ← (( do (AArch64_GetTranslationStartInfo regime ss accdesc address 1) ) : SailM
          TranslationStartInfo )
        (start_translation tsi)
        let w__22 ← (( do (AArch64_S1Translate fault regime address aligned accdesc) ) : SailM
          (FaultRecord × AddressDescriptor) )
        let (tup__0, tup__1) := (w__22 : (FaultRecord × AddressDescriptor))
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        (pure ((addrdesc, fault)))) ) : SailM (AddressDescriptor × FaultRecord) )
  let (addrdesc, fault) ← (( do
    if (((BEq.beq stage TranslationStage_12) && (BEq.beq fault.statuscode Fault_None)) : Bool)
    then
      (do
        let s1aarch64 ← (( do (undefined_bool_at (← occLabel 2641) ()) ) : SailM Bool )
        let w__26 ← (( do
          if ((← do
               (pure ((← do
                     (ELUsingAArch32 EL1)) && ((BEq.beq regime Regime_EL10) : Bool)))) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        if (w__26 : Bool)
        then
          (do
            let addrdesc : AddressDescriptor :=
              { addrdesc with vaddress := (Sail.BitVec.zeroExtend address 64) }
            let w__27 ← (( do (AArch32_S2Translate fault addrdesc none aligned accdesc) ) : SailM
              (FaultRecord × AddressDescriptor) )
            let (tup__0, tup__1) := (w__27 : (FaultRecord × AddressDescriptor))
            let fault : FaultRecord := tup__0
            let addrdesc : AddressDescriptor := tup__1
            (pure ((addrdesc, fault))))
        else
          (do
            let w__29 ← (( do
              if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
              then
                (do
                  (EL2Enabled ()))
              else (pure false) ) : SailM Bool )
            if (w__29 : Bool)
            then
              (do
                let s1aarch64 : Bool := true
                let w__30 ← (( do
                  (AArch64_S2Translate fault addrdesc s1aarch64 none aligned accdesc) ) : SailM
                  (FaultRecord × AddressDescriptor) )
                let (tup__0, tup__1) := (w__30 : (FaultRecord × AddressDescriptor))
                let fault : FaultRecord := tup__0
                let addrdesc : AddressDescriptor := tup__1
                (pure ((addrdesc, fault))))
            else (pure ((addrdesc, fault)))))
    else (pure ((addrdesc, fault))) ) : SailM (AddressDescriptor × FaultRecord) )
  let is_ATS1Ex : Bool := (bne stage TranslationStage_12)
  let addrdesc ← (( do
    if ((bne fault.statuscode Fault_None) : Bool)
    then
      (do
        let w__31 ← (( do (CreateFaultyAddressDescriptor address fault) ) : SailM
          AddressDescriptor )
        let addrdesc := (w__31 : AddressDescriptor)
        let w__46 ← (( do
          if ((← do
               if ((← do
                    (IsExternalAbort__1 fault)) : Bool)
               then (pure true)
               else
                 (do
                   (pure ((← do
                         let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__33.EL == EL1) : Bool)))) && (fault.s2fs1walk : Bool))))) : Bool)
          then (pure true)
          else
            if ((← do
                 (pure ((← do
                       (HaveRME ())) && ((bne fault.gpcf.gpf GPCF_None) : Bool)))) : Bool)
            then
              if ((← do
                   (ReportAsGPCException fault)) : Bool)
              then (pure true)
              else
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure ((((_get_HCR_EL2_Type_GPF w__39) == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                let w__40 ← (( do readReg PSTATE ) : SailM ProcState )
                                (pure (((w__40.EL == EL1) : Bool))))
                            else (pure false)) && (((el == EL1) || (el == EL0)) : Bool)))) && is_ATS1Ex))
            else (pure false) ) : SailM Bool )
        if (w__46 : Bool)
        then
          (do
            let w__47 ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
            (PAR_EL1_write (Mk_PAR_EL1_Type w__47))
            (AArch64_Abort address addrdesc.fault))
        else (pure (()))
        (pure (addrdesc)))
    else (pure (addrdesc)) ) : SailM AddressDescriptor )
  let addrdesc := addrdesc
  (end_translation addrdesc)
  (AArch64_EncodePAR regime is_ATS1Ex addrdesc)


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_FullTranslate (va : (BitVec 32)) (accdesc : AccessDescriptor) (aligned : Bool) : SailM AddressDescriptor := do
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let regime ← (( do (TranslationRegime accdesc.el) ) : SailM Regime )
  let ipa ← (( do (undefined_AddressDescriptor (← occLabel 2678) ()) ) : SailM AddressDescriptor
    )
  let w__1 ← (( do
    if (((BEq.beq regime Regime_EL2) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__0 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_TTBCR_Type_EAE w__0) == 1#1) : Bool)))) ) : SailM Bool )
  let (fault, ipa) ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (AArch32_S1TranslateLD fault regime va aligned accdesc) ) : SailM
          (FaultRecord × AddressDescriptor) )
        let (tup__0, tup__1) := (w__2 : (FaultRecord × AddressDescriptor))
        let fault : FaultRecord := tup__0
        let ipa : AddressDescriptor := tup__1
        (pure ((fault, ipa))))
    else
      (do
        let (__tup_0, __tup_1, _) ← (( do (AArch32_S1TranslateSD fault regime va aligned accdesc)
          ) : SailM (FaultRecord × AddressDescriptor × SDFType) )
        let fault : FaultRecord := __tup_0
        let ipa : AddressDescriptor := __tup_1
        (pure ((fault, ipa)))) ) : SailM (FaultRecord × AddressDescriptor) )
  if ((bne fault.statuscode Fault_None) : Bool)
  then
    (do
      (CreateFaultyAddressDescriptor (Sail.BitVec.zeroExtend va 64) fault))
  else
    (do
      let w__5 ← (( do
        if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          let ipa : AddressDescriptor := { ipa with vaddress := (Sail.BitVec.zeroExtend va 64) }
          let pa ← (( do (undefined_AddressDescriptor (← occLabel 2679) ()) ) : SailM
            AddressDescriptor )
          let w__6 ← (( do (AArch32_S2Translate fault ipa none aligned accdesc) ) : SailM
            (FaultRecord × AddressDescriptor) )
          let (tup__0, tup__1) := (w__6 : (FaultRecord × AddressDescriptor))
          let fault : FaultRecord := tup__0
          let pa : AddressDescriptor := tup__1
          if ((bne fault.statuscode Fault_None) : Bool)
          then
            (do
              (CreateFaultyAddressDescriptor (Sail.BitVec.zeroExtend va 64) fault))
          else (pure (pa)))
      else (pure (ipa)))


def AArch32_AT (vaddress : (BitVec 32)) (stage_in : TranslationStage) (el : (BitVec 2)) (ataccess : ATAccess) : SailM Unit := do
  let stage : TranslationStage := stage_in
  let ss ← (( do (undefined_SecurityState (← occLabel 2689) ()) ) : SailM SecurityState )
  let regime ← (( do (undefined_Regime (← occLabel 2690) ()) ) : SailM Regime )
  let eae ← (( do (undefined_bool_at (← occLabel 2691) ()) ) : SailM Bool )
  let (eae, regime, ss, stage) ← (( do
    if ((el == EL2) : Bool)
    then
      (let regime : Regime := Regime_EL2
      let eae : Bool := true
      let ss : SecurityState := SS_NonSecure
      (pure ((eae, regime, ss, stage))))
    else
      (do
        if (((BEq.beq stage TranslationStage_1) || ((BEq.beq stage TranslationStage_12) && (! (HaveEL
                   EL2)))) : Bool)
        then
          (do
            let stage : TranslationStage := TranslationStage_1
            let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
            let w__1 ← (( do (SecurityStateAtEL w__0.EL) ) : SailM SecurityState )
            let ss := (w__1 : SecurityState)
            let w__3 ← (( do
              if (((BEq.beq ss SS_Secure) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false) ) : SailM Bool )
            let w__4 : Regime :=
              if (w__3 : Bool)
              then Regime_EL30
              else Regime_EL10
            let regime := (w__4 : Regime)
            let w__5 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
            let eae := (((_get_TTBCR_Type_EAE w__5) == 1#1) : Bool)
            (pure ((eae, regime, ss, stage))))
        else
          (do
            let regime : Regime := Regime_EL10
            let w__8 ← (( do
              if ((HaveAArch32EL EL3) : Bool)
              then
                (do
                  let w__6 ← (( do (TTBCR_NS_read ()) ) : SailM (BitVec 32) )
                  (pure (((_get_TTBCR_Type_EAE w__6) == 1#1))))
              else
                (do
                  let w__7 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
                  (pure (((_get_TTBCR_Type_EAE w__7) == 1#1)))) ) : SailM Bool )
            let eae := (w__8 : Bool)
            let ss : SecurityState := SS_NonSecure
            (pure ((eae, regime, ss, stage))))) ) : SailM
    (Bool × Regime × SecurityState × TranslationStage) )
  let addrdesc ← (( do (undefined_AddressDescriptor (← occLabel 2692) ()) ) : SailM
    AddressDescriptor )
  let sdftype ← (( do (undefined_SDFType (← occLabel 2693) ()) ) : SailM SDFType )
  let aligned : Bool := true
  let supersection : (BitVec 1) := 0#1
  let write : Bool := ((BEq.beq ataccess ATAccess_WritePAN) || (BEq.beq ataccess ATAccess_Write))
  let pan : Bool := ((BEq.beq ataccess ATAccess_WritePAN) || (BEq.beq ataccess ATAccess_ReadPAN))
  let accdesc ← (( do (CreateAccDescAT ss el write pan) ) : SailM AccessDescriptor )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let tsi ← (( do (AArch32_GetTranslationStartInfo regime ss accdesc vaddress 1) ) : SailM
    TranslationStartInfo )
  (start_translation tsi)
  let (addrdesc, fault, supersection) ← (( do
    if (eae : Bool)
    then
      (do
        let w__9 ← (( do (AArch32_S1TranslateLD fault regime vaddress aligned accdesc) ) : SailM
          (FaultRecord × AddressDescriptor) )
        let (tup__0, tup__1) := (w__9 : (FaultRecord × AddressDescriptor))
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        (pure ((addrdesc, fault, supersection))))
    else
      (do
        let w__10 ← (( do (AArch32_S1TranslateSD fault regime vaddress aligned accdesc) ) : SailM
          (FaultRecord × AddressDescriptor × SDFType) )
        let (tup__0, tup__1, tup__2) := (w__10 : (FaultRecord × AddressDescriptor × SDFType))
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        let sdftype : SDFType := tup__2
        let supersection : (BitVec 1) :=
          if ((BEq.beq sdftype SDFType_Supersection) : Bool)
          then 1#1
          else 0#1
        (pure ((addrdesc, fault, supersection)))) ) : SailM
    (AddressDescriptor × FaultRecord × (BitVec 1)) )
  let (addrdesc, fault) ← (( do
    if (((BEq.beq stage TranslationStage_12) && (BEq.beq fault.statuscode Fault_None)) : Bool)
    then
      (do
        let w__11 ← (( do (AArch32_S2Translate fault addrdesc none aligned accdesc) ) : SailM
          (FaultRecord × AddressDescriptor) )
        let (tup__0, tup__1) := (w__11 : (FaultRecord × AddressDescriptor))
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        (pure ((addrdesc, fault))))
    else (pure ((addrdesc, fault))) ) : SailM (AddressDescriptor × FaultRecord) )
  if ((bne fault.statuscode Fault_None) : Bool)
  then
    (do
      let w__17 ← (( do
        if ((← do
             (IsExternalAbort__1 fault)) : Bool)
        then (pure true)
        else
          (do
            (pure ((← do
                  if ((← do
                       let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__13.EL == EL1) : Bool)))) : Bool)
                  then
                    (do
                      (EL2Enabled ()))
                  else (pure false)) && (fault.s2fs1walk : Bool)))) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__18 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
          (PAR_write (Mk_PAR_Type w__18))
          (AArch32_Abort vaddress fault))
      else (pure (())))
  else (pure (()))
  let addrdesc : AddressDescriptor := { addrdesc with fault := fault }
  (end_translation addrdesc)
  let w__26 ← (( do
    if ((← do
         if ((eae : Bool) : Bool)
         then (pure true)
         else
           (do
             if (((BEq.beq stage TranslationStage_12) : Bool) : Bool)
             then
               (do
                 if ((← do
                      let w__19 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((((_get_HCR_Type_VM w__19) == 1#1) : Bool)))) : Bool)
                 then (pure true)
                 else
                   (do
                     let w__20 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                     (pure ((((_get_HCR_Type_DC w__20) == 1#1) : Bool)))))
             else (pure false))) : Bool)
    then (pure true)
    else
      (do
        if ((((BEq.beq stage TranslationStage_1) && (el != EL2)) : Bool) : Bool)
        then
          (do
            let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__24.EL == EL2) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__26 : Bool)
  then
    (do
      (AArch32_EncodePARLD addrdesc ss))
  else
    (do
      (AArch32_EncodePARSD addrdesc supersection ss))


end ArmFull.Functions
