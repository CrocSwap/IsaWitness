import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0037
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0058
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0149
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0169
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0174
import ArmFull.Fn.M0178
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0200
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0209
import ArmFull.Fn.M0212

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

def SPESampleAddContext (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (CollectContextIDR1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg CONTEXTIDR_EL1 ) : SailM (BitVec 64) )
      writeReg SPESampleContextEL1 (Sail.BitVec.extractLsb w__1 31 0)
      writeReg SPESampleContextEL1Valid true)
  else (pure (()))
  let w__2 ← (( do (CollectContextIDR2 ()) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg CONTEXTIDR_EL2 ) : SailM (BitVec 64) )
      writeReg SPESampleContextEL2 (Sail.BitVec.extractLsb w__3 31 0)
      writeReg SPESampleContextEL2Valid true)
  else (pure (()))


def SPESampleAddTimeStamp (_ : Unit) : SailM Unit := do
  let timestamp ← (( do (CollectTimeStamp ()) ) : SailM TimeStamp )
  match timestamp with
  | .TimeStamp_None =>
    (do
      writeReg SPESampleTimestampValid false)
  | _ =>
    (do
      writeReg SPESampleTimestampValid true
      let w__0 ← (( do (GetTimestamp timestamp) ) : SailM (BitVec 64) )
      writeReg SPESampleTimestamp w__0)


def SPEISB (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (BitVec.addInt w__0 4)
  let branch_type : BranchType := BranchType_DIR
  let branch_conditional : Bool := false
  let taken : Bool := false
  let is_isb : Bool := true
  (SPEBranch__1 address branch_type branch_conditional taken is_isb)


def MAIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_MAIR0_Type (← occLabel 2494) ()) ) : SailM MAIR0_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (MAIR0_S_read ()))
  else
    (do
      (MAIR0_NS_read ()))


def MAIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_MAIR1_Type (← occLabel 2496) ()) ) : SailM MAIR1_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (MAIR1_S_read ()))
  else
    (do
      (MAIR1_NS_read ()))


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S1DisabledOutput (fault_in : FaultRecord) (regime : Regime) (va : (BitVec 32)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor) := do
  let fault : FaultRecord := fault_in
  (SetInGuardedPage false)
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2510) ()) ) : SailM
    MemoryAttributes )
  let default_cacheable ← (( do (undefined_bitvector_at (← occLabel 2511) 1) ) : SailM
    (BitVec 1) )
  let w__1 ← (( do
    if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
    then
      (do
        (AArch32_EL2Enabled accdesc.ss))
    else (pure false) ) : SailM Bool )
  let default_cacheable ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let default_cacheable := ((_get_HCR_Type_DC w__3) : (BitVec 1))
            (pure (default_cacheable)))
        else
          (do
            let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let default_cacheable := ((_get_HCR_EL2_Type_DC w__4) : (BitVec 1))
            (pure (default_cacheable))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let memattrs ← (( do
    if ((default_cacheable == 1#1) : Bool)
    then
      (do
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
        let memattrs : MemoryAttributes :=
          { memattrs with inner := { memattrs.inner with attrs := MemAttr_WB } }
        let memattrs : MemoryAttributes :=
          { memattrs with inner := { memattrs.inner with hints := MemHint_RWA } }
        let memattrs : MemoryAttributes :=
          { memattrs with outer := { memattrs.outer with attrs := MemAttr_WB } }
        let memattrs : MemoryAttributes :=
          { memattrs with outer := { memattrs.outer with hints := MemHint_RWA } }
        let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_NSH }
        let w__9 ← (( do
          if ((← do
               if ((← do
                    let w__5 ← (( do (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) :
                      SailM Bool )
                    (pure (((! w__5) : Bool)))) : Bool)
               then
                 (do
                   (HaveMTE2Ext ()))
               else (pure false)) : Bool)
          then
            (do
              let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_DCT w__8) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let memattrs : MemoryAttributes :=
          if (w__9 : Bool)
          then { memattrs with tags := MemTag_AllocationTagged }
          else { memattrs with tags := MemTag_Untagged }
        let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
        (pure (memattrs)))
    else
      (do
        if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
        then
          (do
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
            let memattrs : MemoryAttributes := { memattrs with tags := MemTag_Untagged }
            let w__10 ← (( do (AArch32_S1ICacheEnabled regime) ) : SailM Bool )
            let memattrs : MemoryAttributes :=
              if (w__10 : Bool)
              then
                (let memattrs : MemoryAttributes :=
                  { memattrs with inner := { memattrs.inner with attrs := MemAttr_WT } }
                let memattrs : MemoryAttributes :=
                  { memattrs with inner := { memattrs.inner with hints := MemHint_RA } }
                let memattrs : MemoryAttributes :=
                  { memattrs with outer := { memattrs.outer with attrs := MemAttr_WT } }
                { memattrs with outer := { memattrs.outer with hints := MemHint_RA } })
              else
                (let memattrs : MemoryAttributes :=
                  { memattrs with inner := { memattrs.inner with attrs := MemAttr_NC } }
                { memattrs with outer := { memattrs.outer with attrs := MemAttr_NC } })
            let memattrs : MemoryAttributes := { memattrs with xs := 1#1 }
            (pure (memattrs)))
        else
          (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
          let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRnE }
          let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
          let memattrs : MemoryAttributes := { memattrs with tags := MemTag_Untagged }
          let memattrs : MemoryAttributes := { memattrs with xs := 1#1 }
          (pure (memattrs)))) ) : SailM MemoryAttributes )
  let ntlsmd ← (( do (undefined_bitvector_at (← occLabel 2512) 1) ) : SailM (BitVec 1) )
  let w__11 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let ntlsmd ← (( do
    if (w__11 : Bool)
    then
      (do
        match regime with
        | .Regime_EL30 =>
          (do
            let w__12 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
            let ntlsmd := ((_get_SCTLR_Type_nTLSMD w__12) : (BitVec 1))
            (pure (ntlsmd)))
        | .Regime_EL2 =>
          (do
            let w__13 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
            let ntlsmd := ((_get_HSCTLR_Type_nTLSMD w__13) : (BitVec 1))
            (pure (ntlsmd)))
        | .Regime_EL10 =>
          (do
            if ((HaveAArch32EL EL3) : Bool)
            then
              (do
                let w__14 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
                (pure ((_get_SCTLR_Type_nTLSMD w__14))))
            else
              (do
                let w__15 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                (pure ((_get_SCTLR_Type_nTLSMD w__15)))))
        | _ => (pure (ntlsmd)))
    else (pure (1#1)) ) : SailM (BitVec 1) )
  if ((AArch32_S1HasAlignmentFault accdesc aligned ntlsmd memattrs) : Bool)
  then
    (do
      let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
      let w__17 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
      (pure ((fault, w__17))))
  else
    (do
      let oa ← (( do (undefined_FullAddress (← occLabel 2513) ()) ) : SailM FullAddress )
      let oa : FullAddress := { oa with address := (Sail.BitVec.zeroExtend va 56) }
      let oa : FullAddress :=
        { oa with paspace := if ((BEq.beq accdesc.ss SS_Secure) : Bool)
          then PAS_Secure
          else PAS_NonSecure }
      let ipa ← (( do (CreateAddressDescriptor (Sail.BitVec.zeroExtend va 64) oa memattrs) ) :
        SailM AddressDescriptor )
      (pure ((fault, ipa))))


def AArch32_GetS1TLBContext (regime : Regime) (ss : SecurityState) (va : (BitVec 32)) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2534) ()) ) : SailM TLBContext )
  let tlbcontext ← (( do
    match regime with
    | .Regime_EL2 =>
      (do
        (AArch32_TLBContextEL2 va))
    | .Regime_EL10 =>
      (do
        (AArch32_TLBContextEL10 ss va))
    | .Regime_EL30 =>
      (do
        (AArch32_TLBContextEL30 va))
    | _ => (pure (tlbcontext)) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with includes_s1_name := true }
  let tlbcontext : TLBContext := { tlbcontext with includes_s2_name := false }
  (pure (tlbcontext))


/-- Type quantifiers: k_is_ATS1Ex : Bool -/
def AArch64_EncodePAR (regime : Regime) (is_ATS1Ex : Bool) (addrdesc : AddressDescriptor) : SailM Unit := do
  (PAR_EL1_write (Mk_PAR_EL1_Type (Zeros (n := 128))))
  let paspace : PASpace := addrdesc.paddress.paspace
  let w__0 ← (( do (AArch64_isPARFormatD128 regime is_ATS1Ex) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write (_update_PAR_EL1_Type_D128 w__1 1#1)))
  else
    (do
      let w__2 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write (_update_PAR_EL1_Type_D128 w__2 0#1)))
  if ((! (IsFault addrdesc)) : Bool)
  then
    (do
      let w__3 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write (_update_PAR_EL1_Type_F w__3 0#1))
      let w__4 ← (( do (HaveRME ()) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          if ((BEq.beq regime Regime_EL3) : Bool)
          then
            (do
              match paspace with
              | .PAS_Secure =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b00#2 1 1))
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b00#2 0 0))
                  (PAR_EL1_write __tmp))
              | .PAS_NonSecure =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b01#2 1 1))
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b01#2 0 0))
                  (PAR_EL1_write __tmp))
              | .PAS_Root =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b10#2 1 1))
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b10#2 0 0))
                  (PAR_EL1_write __tmp))
              | .PAS_Realm =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b11#2 1 1))
                  let __tmp : PAR_EL1_Type :=
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b11#2 0 0))
                  (PAR_EL1_write __tmp)))
          else
            (do
              let w__5 ← (( do (SecurityStateForRegime regime) ) : SailM SecurityState )
              if ((BEq.beq w__5 SS_Secure) : Bool)
              then
                (do
                  let w__6 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  let w__7 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                  (PAR_EL1_write (_update_PAR_EL1_Type_NSE w__6 w__7))
                  let w__8 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  (PAR_EL1_write
                    (_update_PAR_EL1_Type_NS w__8
                      (if ((BEq.beq paspace PAS_Secure) : Bool)
                      then 0#1
                      else 1#1))))
              else
                (do
                  let w__9 ← (( do (SecurityStateForRegime regime) ) : SailM SecurityState )
                  if ((BEq.beq w__9 SS_Realm) : Bool)
                  then
                    (do
                      if (((BEq.beq regime Regime_EL10) && is_ATS1Ex) : Bool)
                      then
                        (do
                          let w__10 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__11 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                          (PAR_EL1_write (_update_PAR_EL1_Type_NSE w__10 w__11))
                          let w__12 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__13 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                          (PAR_EL1_write (_update_PAR_EL1_Type_NS w__12 w__13)))
                      else
                        (do
                          let w__14 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__15 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                          (PAR_EL1_write (_update_PAR_EL1_Type_NSE w__14 w__15))
                          let w__16 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          (PAR_EL1_write
                            (_update_PAR_EL1_Type_NS w__16
                              (if ((BEq.beq paspace PAS_Realm) : Bool)
                              then 0#1
                              else 1#1)))))
                  else
                    (do
                      let w__17 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      let w__18 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                      (PAR_EL1_write (_update_PAR_EL1_Type_NSE w__17 w__18))
                      let w__19 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      let w__20 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                      (PAR_EL1_write (_update_PAR_EL1_Type_NS w__19 w__20))))))
      else
        (do
          let w__21 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
          (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__21 11 11 1#1)))
          let w__22 ← (( do (SecurityStateForRegime regime) ) : SailM SecurityState )
          if ((BEq.beq w__22 SS_Secure) : Bool)
          then
            (do
              let w__23 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
              (PAR_EL1_write
                (_update_PAR_EL1_Type_NS w__23
                  (if ((BEq.beq paspace PAS_Secure) : Bool)
                  then 0#1
                  else 1#1))))
          else
            (do
              let w__24 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
              let w__25 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
              (PAR_EL1_write (_update_PAR_EL1_Type_NS w__24 w__25))))
      let w__26 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      let w__27 ← (( do (ReportedPARShareability (PAREncodeShareability addrdesc.memattrs)) ) :
        SailM (BitVec 2) )
      (PAR_EL1_write (_update_PAR_EL1_Type_SH w__26 w__27))
      let w__28 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      if (((_get_PAR_EL1_Type_D128 w__28) == 1#1) : Bool)
      then
        (do
          let w__29 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
          (PAR_EL1_write
            (Mk_PAR_EL1_Type
              (Sail.BitVec.updateSubrange w__29 119 76
                (Sail.BitVec.extractLsb addrdesc.paddress.address 55 12)))))
      else
        (do
          let w__30 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
          (PAR_EL1_write
            (Mk_PAR_EL1_Type
              (Sail.BitVec.updateSubrange w__30 55 12
                (Sail.BitVec.extractLsb addrdesc.paddress.address 55 12)))))
      let w__31 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      let w__32 ← (( do (EncodePARAttrs addrdesc.memattrs) ) : SailM (BitVec 8) )
      let w__33 ← (( do (ReportedPARAttrs w__32) ) : SailM (BitVec 8) )
      (PAR_EL1_write (_update_PAR_EL1_Type_ATTR w__31 w__33))
      let w__34 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      let w__35 ← (( do (__IMPDEF_bit "Non-Faulting PAR") ) : SailM (BitVec 1) )
      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__34 10 10 w__35))))
  else
    (do
      let w__36 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write (_update_PAR_EL1_Type_F w__36 1#1))
      let w__37 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write
        (_update_PAR_EL1_Type_DirtyBit w__37
          (if (addrdesc.fault.dirtybit : Bool)
          then 1#1
          else 0#1)))
      let w__38 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write
        (_update_PAR_EL1_Type_Overlay w__38
          (if (addrdesc.fault.overlay : Bool)
          then 1#1
          else 0#1)))
      let w__39 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write
        (_update_PAR_EL1_Type_TopLevel w__39
          (if (addrdesc.fault.toplevel : Bool)
          then 1#1
          else 0#1)))
      let w__40 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write
        (_update_PAR_EL1_Type_AssuredOnly w__40
          (if (addrdesc.fault.assuredonly : Bool)
          then 1#1
          else 0#1)))
      let w__41 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      let w__42 ← (( do (AArch64_PARFaultStatus addrdesc.fault) ) : SailM (BitVec 6) )
      (PAR_EL1_write (_update_PAR_EL1_Type_FST w__41 w__42))
      let w__43 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write
        (_update_PAR_EL1_Type_PTW w__43
          (if (addrdesc.fault.s2fs1walk : Bool)
          then 1#1
          else 0#1)))
      let w__44 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write
        (_update_PAR_EL1_Type_S w__44
          (if (addrdesc.fault.secondstage : Bool)
          then 1#1
          else 0#1)))
      let w__45 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__45 11 11 1#1)))
      let w__46 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
      let w__47 ← (( do (__IMPDEF_bits 16 "Faulting PAR") ) : SailM (BitVec 16) )
      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__46 63 48 w__47))))


def LR_write (value_name : (BitVec 32)) : SailM Unit := do
  (R_set 14 value_name)


def AArch32_VCRMatch (vaddress : (BitVec 32)) : SailM Bool := do
  let match_word ← (( do (undefined_bitvector_at (← occLabel 2666) 32) ) : SailM (BitVec 32) )
  let ss ← (( do (undefined_SecurityState (← occLabel 2667) ()) ) : SailM SecurityState )
  let val_match ← (( do (undefined_bool_at (← occLabel 2668) ()) ) : SailM Bool )
  let w__4 ← (( do
    if ((← do
         if ((← do
              (UsingAArch32 ())) : Bool)
         then
           (do
             (ELUsingAArch32 EL1))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__3.EL != EL2) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let match_word : (BitVec 32) := (Zeros (n := 32))
      let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      let w__5 ← (( do (ExcVectorBase ()) ) : SailM (BitVec 32) )
      let match_word : (BitVec 32) :=
        if (((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb vaddress 31 5)) == (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
               w__5 31 5))) : Bool)
        then
          (if (((HaveEL EL3) && (BEq.beq ss SS_NonSecure)) : Bool)
          then
            (BitVec.update match_word
              (Sail.Int.toNatChecked (((BitVec.toNat (Sail.BitVec.extractLsb vaddress 4 2)) +i 24)))
              (Bit 1#1))
          else
            (BitVec.update match_word
              (Sail.Int.toNatChecked (((BitVec.toNat (Sail.BitVec.extractLsb vaddress 4 2)) +i 0)))
              (Bit 1#1)))
        else match_word
      let w__10 ← (( do
        (pure ((← do
              if ((← do
                   if (((HaveEL EL3) : Bool) : Bool)
                   then
                     (do
                       (ELUsingAArch32 EL3))
                   else (pure false)) : Bool)
              then
                (do
                  let w__8 ← (( do readReg MVBAR ) : SailM (BitVec 32) )
                  (pure ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb vaddress 31 5)) == (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                        w__8 31 5))) : Bool))))
              else (pure false)) && ((BEq.beq ss SS_Secure) : Bool))) ) : SailM Bool )
      let match_word : (BitVec 32) :=
        if (w__10 : Bool)
        then
          (BitVec.update match_word
            (Sail.Int.toNatChecked (((BitVec.toNat (Sail.BitVec.extractLsb vaddress 4 2)) +i 8)))
            (Bit 1#1))
        else match_word
      let mask ← (( do (undefined_bitvector_at (← occLabel 2669) 32) ) : SailM (BitVec 32) )
      let mask ← (( do
        if ((! (HaveEL EL3)) : Bool)
        then
          (let mask : (BitVec 32) :=
            (((0b00000000#8 +++ 0b00000000#8) +++ 0b00000000#8) +++ 0b11011110#8)
          (pure (mask)))
        else
          (do
            let w__11 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            let mask : (BitVec 32) :=
              if ((! w__11) : Bool)
              then (((0b11011110#8 +++ 0b00000000#8) +++ 0b00000000#8) +++ 0b11011110#8)
              else (((0b11011110#8 +++ 0b00000000#8) +++ 0b11011100#8) +++ 0b11011110#8)
            (pure (mask))) ) : SailM (BitVec 32) )
      let w__12 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
      let match_word : (BitVec 32) := ((match_word &&& w__12) &&& mask)
      let val_match : Bool := (! (IsZero match_word))
      let w__15 ← (( do
        if (((! (IsZero
               ((Sail.BitVec.extractLsb match_word 28 27) +++ ((Sail.BitVec.extractLsb match_word 12
                     11) +++ (Sail.BitVec.extractLsb match_word 4 3))))) : Bool) : Bool)
        then
          (do
            let w__13 ← (( do (DebugTarget ()) ) : SailM (BitVec 2) )
            let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__13 == w__14.EL) : Bool))))
        else (pure false) ) : SailM Bool )
      let val_match ← (( do
        if (w__15 : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_VCMATCHDAPA))
        else (pure (val_match)) ) : SailM Bool )
      if (((! (IsZero (Sail.BitVec.extractLsb vaddress 1 0))) && val_match) : Bool)
      then
        (do
          (ConstrainUnpredictableBool Unpredictable_VCMATCHHALF))
      else (pure (val_match)))
  else (pure (false))


def AArch32_UnalignedAccessFaults (accdesc : AccessDescriptor) : SailM Bool := do
  (pure ((← do
        (pure ((← do
              (pure ((← do
                    (pure ((← do
                          (AlignmentEnforced ())) || (accdesc.a32lsmd : Bool)))) || (accdesc.exclusive : Bool)))) || (accdesc.acqsc : Bool)))) || (accdesc.relsc : Bool)))


def AArch32_ResetGeneralRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 7
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (R_set i w__0)
    (pure loop_vars))
  let loop_i_lower : Nat := 8
  let loop_i_upper : Nat := 12
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__1 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_User w__1)
        let w__2 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_FIQ w__2)
    (pure loop_vars))
  if ((HaveEL EL2) : Bool)
  then
    (do
      let w__3 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (Rmode_set 13 M32_Hyp w__3))
  else (pure (()))
  let loop_i_lower : Nat := 13
  let loop_i_upper : Nat := 14
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_User w__4)
        let w__5 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_FIQ w__5)
        let w__6 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_IRQ w__6)
        let w__7 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_Svc w__7)
        let w__8 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_Abort w__8)
        let w__9 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        (Rmode_set i M32_Undef w__9)
        if ((HaveEL EL3) : Bool)
        then
          (do
            let w__10 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
            (Rmode_set i M32_Monitor w__10))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
