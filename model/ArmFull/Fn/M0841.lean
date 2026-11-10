import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0049
import ArmFull.Fn.M0054
import ArmFull.Fn.M0062
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0174
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0196
import ArmFull.Fn.M0212
import ArmFull.Fn.M0219
import ArmFull.Fn.M0220
import ArmFull.Fn.M0237
import ArmFull.Fn.M0254
import ArmFull.Fn.M0259
import ArmFull.Fn.M0580
import ArmFull.Fn.M0582
import ArmFull.Fn.M0583
import ArmFull.Fn.M0584
import ArmFull.Fn.M0585
import ArmFull.Fn.M0586
import ArmFull.Fn.M0587
import ArmFull.Fn.M0588

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

/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S1TranslateSD (fault_in : FaultRecord) (regime : Regime) (va : (BitVec 32)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor × SDFType) := do
  let ipa ← (( do (undefined_AddressDescriptor (← occLabel 2632) ()) ) : SailM AddressDescriptor
    )
  let fault : FaultRecord := fault_in
  let w__0 ← (( do (AArch32_S1Enabled regime accdesc.ss) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do (undefined_AddressDescriptor (← occLabel 2636) ()) ) : SailM
        AddressDescriptor )
      let ipa : AddressDescriptor := (w__1 : AddressDescriptor)
      let w__2 ← (( do (AArch32_S1DisabledOutput fault regime va aligned accdesc) ) : SailM
        (FaultRecord × AddressDescriptor) )
      let (tup__0, tup__1) := (w__2 : (FaultRecord × AddressDescriptor))
      let fault : FaultRecord := tup__0
      let ipa : AddressDescriptor := tup__1
      let w__3 ← (( do (__UNKNOWN_SDFType ()) ) : SailM SDFType )
      (pure ((fault, ipa, w__3))))
  else
    (do
      let walkstate ← (( do (undefined_TTWState (← occLabel 2633) ()) ) : SailM TTWState )
      let w__4 ← (( do (AArch32_S1WalkSD fault regime accdesc va) ) : SailM
        (FaultRecord × TTWState) )
      let (tup__0, tup__1) := (w__4 : (FaultRecord × TTWState))
      let fault : FaultRecord := tup__0
      let walkstate : TTWState := tup__1
      if ((bne fault.statuscode Fault_None) : Bool)
      then
        (do
          let w__5 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
          let w__6 ← (( do (__UNKNOWN_SDFType ()) ) : SailM SDFType )
          (pure ((fault, w__5, w__6))))
      else
        (do
          let domain ← (( do (AArch32_OutputDomain regime walkstate.domain) ) : SailM (BitVec 2) )
          (SetInGuardedPage false)
          let ntlsmd ← (( do (undefined_bitvector_at (← occLabel 2634) 1) ) : SailM (BitVec 1) )
          let w__7 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
          let ntlsmd ← (( do
            if (w__7 : Bool)
            then
              (do
                match regime with
                | .Regime_EL30 =>
                  (do
                    let w__8 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
                    let ntlsmd := ((_get_SCTLR_Type_nTLSMD w__8) : (BitVec 1))
                    (pure (ntlsmd)))
                | .Regime_EL10 =>
                  (do
                    if ((HaveAArch32EL EL3) : Bool)
                    then
                      (do
                        let w__9 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
                        (pure ((_get_SCTLR_Type_nTLSMD w__9))))
                    else
                      (do
                        let w__10 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                        (pure ((_get_SCTLR_Type_nTLSMD w__10)))))
                | _ => (pure (ntlsmd)))
            else (pure (1#1)) ) : SailM (BitVec 1) )
          let fault ← (( do
            if ((AArch32_S1HasAlignmentFault accdesc aligned ntlsmd walkstate.memattrs) : Bool)
            then
              (let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
              (pure (fault)))
            else
              (do
                if (((! ((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq accdesc.acctype
                           AccessType_DC))) && (domain == Domain_NoAccess)) : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Domain }
                  (pure (fault)))
                else
                  (do
                    if ((domain == Domain_Client) : Bool)
                    then
                      (do
                        let w__12 ← (( do
                          (AArch32_S1SDHasPermissionsFault regime walkstate.permissions
                            walkstate.memattrs.memtype walkstate.baseaddress.paspace accdesc) ) :
                          SailM Bool )
                        let fault : FaultRecord :=
                          if (w__12 : Bool)
                          then { fault with statuscode := Fault_Permission }
                          else fault
                        (pure (fault)))
                    else (pure (fault)))) ) : SailM FaultRecord )
          if ((bne fault.statuscode Fault_None) : Bool)
          then
            (do
              let fault : FaultRecord := { fault with domain := walkstate.domain }
              let w__13 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
              (pure ((fault, w__13, walkstate.sdftype))))
          else
            (do
              let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2635) ()) ) : SailM
                MemoryAttributes )
              let w__19 ← (( do
                if ((← do
                     if (((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                     then
                       (do
                         if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__14 ← (( do (AArch32_S1ICacheEnabled regime) ) : SailM Bool )
                             (pure (((! w__14) : Bool)))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    if ((((bne accdesc.acctype AccessType_IFETCH) && (BEq.beq
                           walkstate.memattrs.memtype MemType_Normal)) : Bool) : Bool)
                    then
                      (do
                        let w__17 ← (( do (AArch32_S1DCacheEnabled regime) ) : SailM Bool )
                        (pure (((! w__17) : Bool))))
                    else (pure false)) ) : SailM Bool )
              let memattrs ← (( do
                if (w__19 : Bool)
                then
                  (do
                    let w__20 ← (( do (NormalNCMemAttr ()) ) : SailM MemoryAttributes )
                    let memattrs := (w__20 : MemoryAttributes)
                    let memattrs : MemoryAttributes := { memattrs with xs := walkstate.memattrs.xs }
                    (pure (memattrs)))
                else
                  (let memattrs : MemoryAttributes := walkstate.memattrs
                  (pure (memattrs))) ) : SailM MemoryAttributes )
              let w__29 ← (( do
                if ((← do
                     if ((← do
                          if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                          then
                            (do
                              (AArch32_EL2Enabled accdesc.ss))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__23 ← (( do
                           (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) : SailM Bool )
                         let w__26 ← (( do
                           if (w__23 : Bool)
                           then
                             (do
                               let w__24 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((_get_HCR_Type_VM w__24))))
                           else
                             (do
                               let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure ((_get_HCR_EL2_Type_VM w__25)))) ) : SailM (BitVec 1) )
                         (pure (((w__26 == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__28 ← (( do (__IMPDEF_boolean "Apply effective shareability at stage 1")
                      ) : SailM Bool )
                    (pure (((! w__28) : Bool))))
                else (pure false) ) : SailM Bool )
              let memattrs : MemoryAttributes :=
                if (w__29 : Bool)
                then { memattrs with shareability := walkstate.memattrs.shareability }
                else { memattrs with shareability := (EffectiveShareability memattrs) }
              let oa ← (( do (AArch32_SDStageOA walkstate.baseaddress va walkstate.sdftype) ) :
                SailM FullAddress )
              let ipa ← (( do (CreateAddressDescriptor (Sail.BitVec.zeroExtend va 64) oa memattrs)
                ) : SailM AddressDescriptor )
              (pure ((fault, ipa, walkstate.sdftype))))))


/-- Type quantifiers: CRm : Int, CRn : Int, nreg : Int -/
def AArch32_CheckCP15InstrCoarseTraps (CRn : Int) (nreg : Int) (CRm : Int) : SailM Unit := do
  let major ← (( do (undefined_int_at (← occLabel 2712) ()) ) : SailM Int )
  let w__6 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        if ((← do
             let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
             (pure (((! w__1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                (pure (((! w__3) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (AArch64_CheckCP15InstrCoarseTraps CRn nreg CRm))
  else (pure (()))
  let trapped_encoding : Bool :=
    ((((CRn == 9) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || (CRm == 8)))))))) || ((CRn == 10) && ((CRm == 0) || ((CRm == 1) || ((CRm == 4) || (CRm == 8)))))) || ((CRn == 11) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 3) || ((CRm == 4) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || ((CRm == 8) || (CRm == 15))))))))))))
  let w__11 ← (( do
    if ((← do
         if ((← do
              let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__7.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__8.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let major : Int :=
        if ((nreg == 1) : Bool)
        then CRn
        else CRm
      ArmFull.assert ((0 ≤b major) && (major <b 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:41574.54-41574.55"
      let w__17 ← (( do
        if ((← do
             if (((! ((major == 4) || (major == 14))) : Bool) : Bool)
             then
               (do
                 let w__12 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__12
                         (Sail.Int.toNatChecked (major)))])) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (pure ((← do
                (pure ((← do
                      let w__14 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((((_get_HCR_Type_TIDCP w__14) == 1#1) : Bool)))) && ((nreg == 1) : Bool)))) && trapped_encoding))
        ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__20 ← (( do
            if ((← do
                 let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__18.EL == EL0) : Bool)))) : Bool)
            then
              (do
                (__IMPDEF_boolean "UNDEF unallocated CP15 access at EL0"))
            else (pure false) ) : SailM Bool )
          if (w__20 : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (()))
          let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch32_SystemAccessTrap M32_Hyp (BitVec.toNat 0x3#4)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4))))
      else (pure (())))
  else (pure (()))


def AArch32_CheckAdvSIMDOrFPRegisterTraps (reg : (BitVec 4)) : SailM Unit := do
  let tid0 ← (( do (undefined_bitvector_at (← occLabel 2774) 1) ) : SailM (BitVec 1) )
  let tid3 ← (( do (undefined_bitvector_at (← occLabel 2775) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL1) : Bool)))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
      let tid0 ← (( do
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_HCR_Type_TID0 w__4))))
        else
          (do
            let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_HCR_EL2_Type_TID0 w__5)))) ) : SailM (BitVec 1) )
      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
      let tid3 ← (( do
        if (w__6 : Bool)
        then
          (do
            let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_HCR_Type_TID3 w__7))))
        else
          (do
            let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_HCR_EL2_Type_TID3 w__8)))) ) : SailM (BitVec 1) )
      if ((((tid0 == 1#1) && (reg == 0b0000#4)) || ((tid3 == 1#1) && ((reg == 0b0101#4) || ((reg == 0b0110#4) || (reg == 0b0111#4))))) : Bool)
      then
        (do
          let w__9 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch32_SystemAccessTrap M32_Hyp (BitVec.toNat 0x8#4)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x8#4))))
      else (pure (())))
  else (pure (()))


def AArch32_SoftwareBreakpoint (immediate : (BitVec 16)) : SailM Unit := do
  let w__8 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__1 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__1) : Bool))))
              else (pure false)) : Bool)
         then
           (do
             if ((← do
                  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__4 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_MDCR_EL2_Type_TDE w__4) == 1#1) : Bool)))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__7 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__7) : Bool)))) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_SoftwareBreakpoint immediate))
  else (pure (()))
  let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let vaddress ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  let fault : FaultRecord := { fault with statuscode := Fault_Debug }
  let fault : FaultRecord := { fault with debugmoe := DebugException_BKPT }
  (AArch32_Abort vaddress fault)


def AArch32_CheckPCAlignment (_ : Unit) : SailM Unit := do
  let pc ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let w__2 ← (( do
    (pure ((← do
          (pure ((← do
                let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
                (pure (((BEq.beq w__0 InstrSet_A32) : Bool)))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    pc 1)])) == 1#1) : Bool)))) || (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              pc 0)])) == 1#1) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (AArch32_GeneralExceptionsToAArch64 ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (AArch64_PCAlignmentFault ()))
      else (pure (()))
      let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
      let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
      let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
      (AArch32_Abort pc fault))
  else (pure (()))


def TakeUnmaskedSErrorInterrupts (_ : Unit) : SailM Unit := do
  let interrupt_req ← (( do (undefined_InterruptReq (← occLabel 2881) ()) ) : SailM InterruptReq
    )
  let interrupt_req : InterruptReq := { interrupt_req with take_SE := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vSE := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_FIQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vFIQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_IRQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vIRQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with iesb_req := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_SE := true }
  let interrupt_req : InterruptReq := { interrupt_req with take_vSE := true }
  let interrupt_taken ← (( do (TakePendingInterrupts interrupt_req) ) : SailM Bool )
  (pure (()))


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch32_AutoGen_SysRegWrite64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((CRm == 0b1100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
  then
    (do
      (ICC_SGI1R_SysRegWrite64_e5d73969c7266f22 el coproc opc1 CRm t t2))
  else
    (do
      if ((((CRm == 0b1100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
      then
        (do
          (ICC_SGI0R_SysRegWrite64_3055f033253258da el coproc opc1 CRm t t2))
      else
        (do
          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
          then
            (do
              (CNTVOFF_SysRegWrite64_772809c07f941c73 el coproc opc1 CRm t t2))
          else
            (do
              if ((((CRm == 0b1100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
              then
                (do
                  (ICC_ASGI1R_SysRegWrite64_29140bc551f7529b el coproc opc1 CRm t t2))
              else
                (do
                  if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                  then
                    (do
                      (CNTHV_CVAL_SysRegWrite64_e72c3c45ec57bc51 el coproc opc1 CRm t t2))
                  else
                    (do
                      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                      then
                        (do
                          (CNTHPS_CVAL_SysRegWrite64_34fa93164860ce59 el coproc opc1 CRm t t2))
                      else
                        (do
                          if ((((CRm == 0b0111#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                          then
                            (do
                              (PAR_SysRegWrite64_867d7cbf8d644296 el coproc opc1 CRm t t2))
                          else
                            (do
                              if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                              then
                                (do
                                  (CNTHP_CVAL_SysRegWrite64_558ce8493f8ab75e el coproc opc1 CRm t t2))
                              else
                                (do
                                  if ((((CRm == 0b1001#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                  then
                                    (do
                                      (PMCCNTR_SysRegWrite64_51a4ab1690d771a1 el coproc opc1 CRm t
                                        t2))
                                  else
                                    (do
                                      if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                      then
                                        (do
                                          (TTBR1_SysRegWrite64_7d88e184b6073f76 el coproc opc1 CRm t
                                            t2))
                                      else
                                        (do
                                          if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                          then
                                            (do
                                              (HTTBR_SysRegWrite64_3e34efab7aaa3ec6 el coproc opc1
                                                CRm t t2))
                                          else
                                            (do
                                              if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                              then
                                                (do
                                                  (TTBR0_SysRegWrite64_c1a707eccbf8dd96 el coproc
                                                    opc1 CRm t t2))
                                              else
                                                (do
                                                  if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                  then
                                                    (do
                                                      (VTTBR_SysRegWrite64_ab86e13c6c48344f el
                                                        coproc opc1 CRm t t2))
                                                  else
                                                    (do
                                                      if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                      then
                                                        (do
                                                          (AMEVCNTR0_SysRegWrite64_125e5d1a241e0a34
                                                            el coproc opc1 CRm t t2))
                                                      else
                                                        (do
                                                          if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                          then
                                                            (do
                                                              (AMEVCNTR0_SysRegWrite64_a509b10e64184e5e
                                                                el coproc opc1 CRm t t2))
                                                          else
                                                            (do
                                                              if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                              then
                                                                (do
                                                                  (AMEVCNTR0_SysRegWrite64_ffac5e218d5b074d
                                                                    el coproc opc1 CRm t t2))
                                                              else
                                                                (do
                                                                  if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                  then
                                                                    (do
                                                                      (AMEVCNTR0_SysRegWrite64_00363288e0ffc481
                                                                        el coproc opc1 CRm t t2))
                                                                  else
                                                                    (do
                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                      then
                                                                        (do
                                                                          (AMEVCNTR1_SysRegWrite64_469c861805be726d
                                                                            el coproc opc1 CRm t t2))
                                                                      else
                                                                        (do
                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                          then
                                                                            (do
                                                                              (AMEVCNTR1_SysRegWrite64_caa18a28b827223b
                                                                                el coproc opc1 CRm t
                                                                                t2))
                                                                          else
                                                                            (do
                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (AMEVCNTR1_SysRegWrite64_6aa1c0a95da044bc
                                                                                    el coproc opc1
                                                                                    CRm t t2))
                                                                              else
                                                                                (do
                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (AMEVCNTR1_SysRegWrite64_3cf44094d12f6f9a
                                                                                        el coproc
                                                                                        opc1 CRm t
                                                                                        t2))
                                                                                  else
                                                                                    (do
                                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (AMEVCNTR1_SysRegWrite64_8df7cb996ace4301
                                                                                            el
                                                                                            coproc
                                                                                            opc1 CRm
                                                                                            t t2))
                                                                                      else
                                                                                        (do
                                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (AMEVCNTR1_SysRegWrite64_1415f513493b61c8
                                                                                                el
                                                                                                coproc
                                                                                                opc1
                                                                                                CRm
                                                                                                t t2))
                                                                                          else
                                                                                            (do
                                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (AMEVCNTR1_SysRegWrite64_ec5133758c2bd694
                                                                                                    el
                                                                                                    coproc
                                                                                                    opc1
                                                                                                    CRm
                                                                                                    t
                                                                                                    t2))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (AMEVCNTR1_SysRegWrite64_683d5eccd985c418
                                                                                                        el
                                                                                                        coproc
                                                                                                        opc1
                                                                                                        CRm
                                                                                                        t
                                                                                                        t2))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (AMEVCNTR1_SysRegWrite64_a0a98205a8cc86f4
                                                                                                            el
                                                                                                            coproc
                                                                                                            opc1
                                                                                                            CRm
                                                                                                            t
                                                                                                            t2))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (AMEVCNTR1_SysRegWrite64_8ea485840df13e8b
                                                                                                                el
                                                                                                                coproc
                                                                                                                opc1
                                                                                                                CRm
                                                                                                                t
                                                                                                                t2))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (AMEVCNTR1_SysRegWrite64_9589f0d5bbc35480
                                                                                                                    el
                                                                                                                    coproc
                                                                                                                    opc1
                                                                                                                    CRm
                                                                                                                    t
                                                                                                                    t2))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (AMEVCNTR1_SysRegWrite64_18488936f5130285
                                                                                                                        el
                                                                                                                        coproc
                                                                                                                        opc1
                                                                                                                        CRm
                                                                                                                        t
                                                                                                                        t2))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (AMEVCNTR1_SysRegWrite64_80489a0c42f5990f
                                                                                                                            el
                                                                                                                            coproc
                                                                                                                            opc1
                                                                                                                            CRm
                                                                                                                            t
                                                                                                                            t2))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (AMEVCNTR1_SysRegWrite64_4a0c18bf00eccda4
                                                                                                                                el
                                                                                                                                coproc
                                                                                                                                opc1
                                                                                                                                CRm
                                                                                                                                t
                                                                                                                                t2))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (AMEVCNTR1_SysRegWrite64_06329c412b3ab5ff
                                                                                                                                    el
                                                                                                                                    coproc
                                                                                                                                    opc1
                                                                                                                                    CRm
                                                                                                                                    t
                                                                                                                                    t2))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (AMEVCNTR1_SysRegWrite64_8a065d943b8f719e
                                                                                                                                        el
                                                                                                                                        coproc
                                                                                                                                        opc1
                                                                                                                                        CRm
                                                                                                                                        t
                                                                                                                                        t2))
                                                                                                                                  else
                                                                                                                                    sailThrow ((Error_Undefined
                                                                                                                                      ()))))))))))))))))))))))))))))))))))


end ArmFull.Functions
