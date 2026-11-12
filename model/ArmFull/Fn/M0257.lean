import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0019
import ArmFull.Fn.M0022
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0118
import ArmFull.Fn.M0119
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0152
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0171
import ArmFull.Fn.M0173
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0185
import ArmFull.Fn.M0188
import ArmFull.Fn.M0202
import ArmFull.Fn.M0204
import ArmFull.Fn.M0217
import ArmFull.Fn.M0227
import ArmFull.Fn.M0237
import ArmFull.Fn.M0247
import ArmFull.Fn.M0252

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

def CheckSPAlignment (_ : Unit) : SailM Unit := do
  let sp ← (( do (SP_read ()) ) : SailM (BitVec 64) )
  let stack_align_check ← (( do (undefined_bool_at (← occLabel 1352) ()) ) : SailM Bool )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let stack_align_check ← (( do
    if ((w__0.EL == EL0) : Bool)
    then
      (do
        let w__1 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        let stack_align_check := (((_get_SCTLRType_SA0 w__1) != 0#1) : Bool)
        (pure (stack_align_check)))
    else
      (do
        let w__2 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        let stack_align_check := (((_get_SCTLRType_SA w__2) != 0#1) : Bool)
        (pure (stack_align_check))) ) : SailM Bool )
  if ((stack_align_check && (sp != (Align_bits sp 16))) : Bool)
  then
    (do
      (AArch64_SPAlignmentFault ()))
  else (pure (()))


def AArch64_TagCheckFault (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) : SailM Unit := do
  let tcf ← (( do (AArch64_EffectiveTCF accdesc.el) ) : SailM (BitVec 2) )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_TagCheck }
  match tcf with
  | 0b00 => (pure (()))
  | 0b01 =>
    (do
      (AArch64_RaiseTagCheckFault vaddress fault))
  | 0b10 =>
    (do
      let w__0 ← (( do (HaveMTEAsyncExt ()) ) : SailM Bool )
      if (w__0 : Bool)
      then
        (do
          (AArch64_ReportTagCheckFault accdesc.el
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access vaddress 55)]))))
      else (pure (())))
  | _ =>
    (do
      let w__1 ← (( do (HaveMTEAsymFaultExt ()) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          if (accdesc.read : Bool)
          then
            (do
              (AArch64_RaiseTagCheckFault vaddress fault))
          else
            (do
              (AArch64_ReportTagCheckFault accdesc.el
                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access vaddress 55)])))))
      else (pure (())))


/-- Type quantifiers: N : Nat, 10 < N -/
def AArch64_S1Walk (fault_in : FaultRecord) (walkparams : S1TTWParams) (va : (BitVec 64)) (regime : Regime) (accdesc : AccessDescriptor) (N : Nat) : SailM (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) := SailME.run do
  let fault : FaultRecord := fault_in
  let s1aarch64 ← (( do (undefined_bool_at (← occLabel 1591) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
  let aligned ← (( do (undefined_bool_at (← occLabel 1592) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1593) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBContext )
  let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 1594) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
  let w__0 ← (( do readReg __tlb_enabled ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
  let (fault, tlbcontext, tlbrecord) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (AArch64_GetS1TLBContext regime accdesc.ss va walkparams.tgx) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBContext )
        let tlbcontext := (w__1 : TLBContext)
        let tlbentry ← (( do (S1TLBLookup tlbcontext) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBLine )
        let tlbrecord : TLBRecord := tlbentry.tlbrecord
        let oa ← (( do (StageOA va walkparams.d128 walkparams.tgx tlbrecord.walkstate) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FullAddress )
        let w__4 ← (( do
          (pure ((← do
                if ((tlbentry.valid_name : Bool) : Bool)
                then
                  (do
                    let w__2 ← (( do
                      (AArch64_OAOutOfRange oa.address walkparams.d128 walkparams.ps walkparams.tgx)
                      ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                    (pure (((! w__2) : Bool))))
                else (pure false)) && ((! ((((((walkparams.ha +++ walkparams.hd) == 0b11#2) && ((walkparams.pie == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                tlbrecord.s1descriptor 51)])) == 1#1))) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                            tlbrecord.s1descriptor 7)])) == 1#1)) && accdesc.write) && (! ((BEq.beq
                        accdesc.acctype AccessType_AT) || ((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq
                          accdesc.acctype AccessType_DC)))))) : Bool))) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
        let fault ← (( do
          if (w__4 : Bool)
          then
            (do
              let fault : FaultRecord := { fault with level := tlbrecord.walkstate.level }
              ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 128)) "sail-arm/v8_base.sail:27381.59-27381.60"
              let w__5 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
              SailME.throw ((fault, w__5, tlbrecord.walkstate, (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                  tlbrecord.s1descriptor (Sail.Int.toNatChecked ((N -i 1))) 0))) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
              (pure (fault)))
          else (pure (fault)) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FaultRecord )
        (pure ((fault, tlbcontext, tlbrecord))))
    else (pure ((fault, tlbcontext, tlbrecord))) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
    (FaultRecord × TLBContext × TLBRecord) )
  let w__7 ← (( do
    if (((HasUnprivileged regime) : Bool) : Bool)
    then
      (do
        let w__6 ← (( do (AArch64_S1EPD regime va) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec 1) )
        (pure (((w__6 == 1#1) : Bool))))
    else (pure false) ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
  if (w__7 : Bool)
  then
    (do
      let fault : FaultRecord := { fault with statuscode := Fault_Translation }
      let fault : FaultRecord := { fault with level := 0 }
      let w__8 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
      let w__9 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
      let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
      (pure ((fault, w__8, w__9, w__10))))
  else
    (do
      let walkstate ← (( do (AArch64_S1InitialTTWState walkparams va regime accdesc.ss) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
      let startlevel : Int := walkstate.level
      let descriptor ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1595)
          (Sail.Int.toNatChecked (N)))) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
      let walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 1596) ()) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
      let skl : (BitVec 2) := 0b00#2
      let walkaddress : AddressDescriptor := { walkaddress with vaddress := va }
      let w__11 ← (( do (AArch64_TTWalkMECID walkparams.emec regime accdesc.ss) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec 16) )
      let walkaddress := ({ walkaddress with mecid := w__11 } : AddressDescriptor)
      let w__12 ← (( do (AArch64_S1DCacheEnabled regime) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
      let walkaddress ← (( do
        if ((! w__12) : Bool)
        then
          (do
            let w__13 ← (( do (NormalNCMemAttr ()) ) : SailME
              (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) MemoryAttributes )
            let walkaddress := ({ walkaddress with memattrs := w__13 } : AddressDescriptor)
            let walkaddress : AddressDescriptor :=
              { walkaddress with memattrs := { walkaddress.memattrs with xs := walkstate.memattrs.xs } }
            (pure (walkaddress)))
        else
          (let walkaddress : AddressDescriptor :=
            { walkaddress with memattrs := walkstate.memattrs }
          (pure (walkaddress))) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
      let w__19 ← (( do
        if ((← do
             if ((← do
                  if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                  then
                    (do
                      (EL2Enabled ()))
                  else (pure false)) : Bool)
             then
               (do
                 let w__16 ← (( do readReg HCR_EL2 ) : SailME
                   (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_VM w__16) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__18 ← (( do (__IMPDEF_boolean "Apply effective shareability at stage 1") ) :
              SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
            (pure (((! w__18) : Bool))))
        else (pure false) ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
        Bool )
      let walkaddress : AddressDescriptor :=
        if (w__19 : Bool)
        then
          { walkaddress with memattrs := { walkaddress.memattrs with shareability := walkstate.memattrs.shareability } }
        else
          { walkaddress with memattrs := { walkaddress.memattrs with shareability := (EffectiveShareability
                walkaddress.memattrs) } }
      let walkaddress : AddressDescriptor := { walkaddress with tlbcontext := tlbcontext }
      let s2fs1mro : Bool := false
      let desctype ← (( do (undefined_DescriptorType (← occLabel 1597) ()) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) DescriptorType )
      let descaddress ← (( do
        (AArch64_S1SLTTEntryAddress walkstate.level walkparams va walkstate.baseaddress) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FullAddress )
      let w__20 ← (( do
        (AArch64_OAOutOfRange descaddress.address walkparams.d128 walkparams.ps walkparams.tgx) ) :
        SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
      if (w__20 : Bool)
      then
        (do
          let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
          let fault : FaultRecord := { fault with level := 0 }
          let w__21 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
          let w__22 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
          let w__23 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
          (pure ((fault, w__21, w__22, w__23))))
      else
        (do
          let (aligned, descaddress, descriptor, desctype, fault, s1aarch64, s2fs1mro, skl, walkaddress, walkstate) ← (( do
            let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (aligned, descaddress, descriptor, desctype, fault, s1aarch64, s2fs1mro, skl, walkaddress, walkstate) => (pure (BEq.beq
                desctype DescriptorType_Leaf))) (aligned, descaddress, descriptor, desctype, fault, s1aarch64, s2fs1mro, skl, walkaddress, walkstate)
              fun (aligned, descaddress, descriptor, desctype, fault, s1aarch64, s2fs1mro, skl, walkaddress, walkstate) => do
                let fault : FaultRecord := { fault with level := walkstate.level }
                let walkaddress : AddressDescriptor := { walkaddress with paddress := descaddress }
                let toplevel : Bool := (walkstate.level == startlevel)
                let varange : VARange := (AArch64_GetVARange va)
                let walkaccess ← (( do (CreateAccDescS1TTW toplevel varange accdesc) ) : SailME
                  (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AccessDescriptor )
                let translation_info : TranslationInfo :=
                  { regime := regime
                    vmid := none
                    asid := none
                    va := walkaddress.vaddress
                    s1level := (some walkstate.level)
                    s2info := none
                    s1params := (some walkparams)
                    s2params := none
                    memattrs := walkaddress.memattrs }
                let s2fault ← (( do (undefined_FaultRecord (← occLabel 1603) ()) ) : SailME
                  (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FaultRecord )
                let s2walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 1604) ()) ) :
                  SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                  AddressDescriptor )
                let w__25 ← (( do
                  if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                  then
                    (do
                      (EL2Enabled ()))
                  else (pure false) ) : SailME
                  (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                let (aligned, descriptor, fault, s1aarch64, s2fault, s2fs1mro) ← (( do
                  if (w__25 : Bool)
                  then
                    (do
                      let s1aarch64 : Bool := true
                      let aligned : Bool := true
                      let w__26 ← (( do
                        (AArch64_S2Translate fault walkaddress s1aarch64 (some walkstate.level)
                          aligned walkaccess) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                        (FaultRecord × AddressDescriptor) )
                      let (tup__0, tup__1) := (w__26 : (FaultRecord × AddressDescriptor))
                      let s2fault : FaultRecord := tup__0
                      let s2walkaddress : AddressDescriptor := tup__1
                      let (descriptor, fault, s2fs1mro) ← (( do
                        if ((bne s2fault.statuscode Fault_None) : Bool)
                        then
                          (do
                            let w__27 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                              AddressDescriptor )
                            let w__28 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState
                              )
                            let w__29 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) )
                              : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                              (BitVec N) )
                            SailME.throw ((s2fault, w__27, w__28, w__29) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                            (pure ((descriptor, fault, s2fs1mro))))
                        else
                          (do
                            let s2fs1mro : Bool := s2walkaddress.s2fs1mro
                            ArmFull.assert (((N == 32) || (N == 64)) || (N == 128)) "sail-arm/v8_base.sail:27445.50-27445.51"
                            let w__30 ← (( do
                              ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (FetchDescriptor
                                walkparams.ee s2walkaddress walkaccess fault N translation_info)) )
                              : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                              (FaultRecord × (BitVec N)) )
                            let (tup__0, tup__1) := (w__30 : (FaultRecord × (BitVec N)))
                            let fault : FaultRecord := tup__0
                            let descriptor : (BitVec N) := tup__1
                            (pure ((descriptor, fault, s2fs1mro)))) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                        ((BitVec N) × FaultRecord × Bool) )
                      (pure ((aligned, descriptor, fault, s1aarch64, s2fault, s2fs1mro))))
                  else
                    (do
                      ArmFull.assert (((N == 32) || (N == 64)) || (N == 128)) "sail-arm/v8_base.sail:27448.50-27448.51"
                      let w__31 ← (( do
                        ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (FetchDescriptor
                          walkparams.ee walkaddress walkaccess fault N translation_info)) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                        (FaultRecord × (BitVec N)) )
                      let (tup__0, tup__1) := (w__31 : (FaultRecord × (BitVec N)))
                      let fault : FaultRecord := tup__0
                      let descriptor : (BitVec N) := tup__1
                      (pure ((aligned, descriptor, fault, s1aarch64, s2fault, s2fs1mro)))) ) :
                  SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                  (Bool × (BitVec N) × FaultRecord × Bool × FaultRecord × Bool) )
                let (aligned, descaddress, descriptor, desctype, fault, s1aarch64, skl, walkstate) ← (( do
                  if ((bne fault.statuscode Fault_None) : Bool)
                  then
                    (do
                      let w__32 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                        AddressDescriptor )
                      let w__33 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
                      let w__34 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) :
                        SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                        (BitVec N) )
                      SailME.throw ((fault, w__32, w__33, w__34) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                      (pure ((aligned, descaddress, descriptor, desctype, fault, s1aarch64, skl, walkstate))))
                  else
                    (do
                      let new_descriptor ← (( do
                        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1605)
                          (Sail.Int.toNatChecked (N)))) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
                      let (aligned, descaddress, descriptor, desctype, fault, new_descriptor, s1aarch64, s2fault, skl, walkstate) ← (( do
                        let loop_vars_1 ← sailUntilFuelM (fuel := 1048576) (fun (aligned, descaddress, descriptor, desctype, fault, new_descriptor, s1aarch64, s2fault, skl, walkstate) => (pure (new_descriptor == descriptor))) (aligned, descaddress, descriptor, desctype, fault, new_descriptor, s1aarch64, s2fault, skl, walkstate)
                          fun (aligned, descaddress, descriptor, desctype, fault, new_descriptor, s1aarch64, s2fault, skl, walkstate) => do
                            let new_descriptor : (BitVec N) := descriptor
                            let w__35 ← (( do
                              (AArch64_DecodeDescriptorType descriptor walkparams.d128 walkparams.ds
                                walkparams.tgx walkstate.level) ) : SailME
                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                              DescriptorType )
                            let desctype := (w__35 : DescriptorType)
                            let (descaddress, fault, new_descriptor, skl, walkstate) ← (( do
                              match desctype with
                              | .DescriptorType_Table =>
                                (do
                                  let w__36 ← (( do
                                    (AArch64_S1NextWalkStateTable walkstate s2fs1mro regime
                                      walkparams descriptor) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    TTWState )
                                  let walkstate := (w__36 : TTWState)
                                  let w__37 ← (( do
                                    if ((walkparams.d128 == 1#1) : Bool)
                                    then
                                      (do
                                        ArmFull.assert (110 <b N) "sail-arm/v8_base.sail:27462.49-27462.50"
                                        (pure ((Sail.BitVec.extractLsb descriptor 110 109))))
                                    else (pure (0b00#2)) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    (BitVec 2) )
                                  let skl := (w__37 : (BitVec 2))
                                  let w__38 ← (( do
                                    (AArch64_TTEntryAddress walkstate.level walkparams.d128 skl
                                      walkparams.tgx walkparams.txsz va walkstate.baseaddress) ) :
                                    SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    FullAddress )
                                  let descaddress := (w__38 : FullAddress)
                                  let w__39 ← (( do
                                    (AArch64_OAOutOfRange descaddress.address walkparams.d128
                                      walkparams.ps walkparams.tgx) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    Bool )
                                  let (fault, new_descriptor) ← (( do
                                    if (w__39 : Bool)
                                    then
                                      (do
                                        let fault : FaultRecord :=
                                          { fault with statuscode := Fault_AddressSize }
                                        let w__40 ← (( do (__UNKNOWN_AddressDescriptor ()) ) :
                                          SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          AddressDescriptor )
                                        let w__41 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          TTWState )
                                        let w__42 ← (( do
                                          ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) :
                                          SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          (BitVec N) )
                                        SailME.throw ((fault, w__40, w__41, w__42) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                                        (pure ((fault, new_descriptor))))
                                    else
                                      (do
                                        let new_descriptor ← (( do
                                          if ((walkparams.haft == 1#1) : Bool)
                                          then
                                            (do
                                              ArmFull.assert (10 <b N) "sail-arm/v8_base.sail:27471.48-27471.49"
                                              let new_descriptor : (BitVec N) :=
                                                (BitVec.update new_descriptor 10 (Bit 1#1))
                                              (pure (new_descriptor)))
                                          else (pure (new_descriptor)) ) : SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          (BitVec N) )
                                        let w__44 ← (( do
                                          if ((((walkparams.d128 == 1#1) && (skl != 0b00#2)) : Bool) : Bool)
                                          then
                                            (do
                                              (AArch64_BlocknTFaults walkparams.d128 descriptor))
                                          else (pure false) ) : SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          Bool )
                                        let fault ← (( do
                                          if (w__44 : Bool)
                                          then
                                            (do
                                              let fault : FaultRecord :=
                                                { fault with statuscode := Fault_Translation }
                                              let w__45 ← (( do (__UNKNOWN_AddressDescriptor ()) )
                                                : SailME
                                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                                AddressDescriptor )
                                              let w__46 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                                TTWState )
                                              let w__47 ← (( do
                                                ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) )
                                                : SailME
                                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                                (BitVec N) )
                                              SailME.throw ((fault, w__45, w__46, w__47) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                                              (pure (fault)))
                                          else (pure (fault)) ) : SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          FaultRecord )
                                        (pure ((fault, new_descriptor)))) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    (FaultRecord × (BitVec N)) )
                                  (pure ((descaddress, fault, new_descriptor, skl, walkstate))))
                              | .DescriptorType_Leaf =>
                                (do
                                  let w__48 ← (( do
                                    (AArch64_S1NextWalkStateLeaf walkstate s2fs1mro regime
                                      accdesc.ss walkparams descriptor) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    TTWState )
                                  let walkstate := (w__48 : TTWState)
                                  (pure ((descaddress, fault, new_descriptor, skl, walkstate))))
                              | .DescriptorType_Invalid =>
                                (do
                                  let fault : FaultRecord :=
                                    { fault with statuscode := Fault_Translation }
                                  let w__49 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    AddressDescriptor )
                                  let w__50 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    TTWState )
                                  let w__51 ← (( do
                                    ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    (BitVec N) )
                                  SailME.throw ((fault, w__49, w__50, w__51) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                                  (pure ((descaddress, fault, new_descriptor, skl, walkstate)))) ) :
                              SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                              (FullAddress × FaultRecord × (BitVec N) × (BitVec 2) × TTWState) )
                            let (aligned, descriptor, fault, s1aarch64, s2fault) ← (( do
                              if ((new_descriptor != descriptor) : Bool)
                              then
                                (do
                                  let descpaddr ← (( do
                                    (undefined_AddressDescriptor (← occLabel 1607) ()) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    AddressDescriptor )
                                  let descaccess ← (( do (CreateAccDescTTEUpdate accdesc) ) :
                                    SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    AccessDescriptor )
                                  let w__53 ← (( do
                                    if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                                    then
                                      (do
                                        (EL2Enabled ()))
                                    else (pure false) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    Bool )
                                  let (aligned, descpaddr, s1aarch64, s2fault) ← (( do
                                    if (w__53 : Bool)
                                    then
                                      (do
                                        let s1aarch64 : Bool := true
                                        let aligned : Bool := true
                                        let w__54 ← (( do
                                          (AArch64_S2Translate fault walkaddress s1aarch64
                                            (some walkstate.level) aligned descaccess) ) : SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          (FaultRecord × AddressDescriptor) )
                                        let (tup__0, tup__1) :=
                                          (w__54 : (FaultRecord × AddressDescriptor))
                                        let s2fault : FaultRecord := tup__0
                                        let descpaddr : AddressDescriptor := tup__1
                                        if ((bne s2fault.statuscode Fault_None) : Bool)
                                        then
                                          (do
                                            let w__55 ← (( do (__UNKNOWN_AddressDescriptor ()) ) :
                                              SailME
                                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                              AddressDescriptor )
                                            let w__56 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                              TTWState )
                                            let w__57 ← (( do
                                              ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) :
                                              SailME
                                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                              (BitVec N) )
                                            SailME.throw ((s2fault, w__55, w__56, w__57) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N))))
                                        else (pure (()))
                                        (pure ((aligned, descpaddr, s1aarch64, s2fault))))
                                    else
                                      (let descpaddr : AddressDescriptor := walkaddress
                                      (pure ((aligned, descpaddr, s1aarch64, s2fault)))) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    (Bool × AddressDescriptor × Bool × FaultRecord) )
                                  ArmFull.assert ((N == 64) || (N == 128)) "sail-arm/v8_base.sail:27505.50-27505.51"
                                  let w__58 ← (( do
                                    (AArch64_MemSwapTableDesc fault descriptor new_descriptor
                                      walkparams.ee descaccess descpaddr translation_info) ) :
                                    SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    (FaultRecord × (BitVec N)) )
                                  let (tup__0, tup__1) := (w__58 : (FaultRecord × (BitVec N)))
                                  let fault : FaultRecord := tup__0
                                  let descriptor : (BitVec N) := tup__1
                                  if ((bne fault.statuscode Fault_None) : Bool)
                                  then
                                    (do
                                      let w__59 ← (( do (__UNKNOWN_AddressDescriptor ()) ) :
                                        SailME
                                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                        AddressDescriptor )
                                      let w__60 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                        TTWState )
                                      let w__61 ← (( do
                                        ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
                                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                        (BitVec N) )
                                      SailME.throw ((fault, w__59, w__60, w__61) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N))))
                                  else (pure (()))
                                  (pure ((aligned, descriptor, fault, s1aarch64, s2fault))))
                              else (pure ((aligned, descriptor, fault, s1aarch64, s2fault))) ) :
                              SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                              (Bool × (BitVec N) × FaultRecord × Bool × FaultRecord) )
                            (pure ((aligned, descaddress, descriptor, desctype, fault, new_descriptor, s1aarch64, s2fault, skl, walkstate)))
                        (pure loop_vars_1) ) : SailME
                        (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                        (Bool × FullAddress × (BitVec N) × DescriptorType × FaultRecord × (BitVec N) × Bool × FaultRecord × (BitVec 2) × TTWState)
                        )
                      (pure ((aligned, descaddress, descriptor, desctype, fault, s1aarch64, skl, walkstate))))
                  ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                  (Bool × FullAddress × (BitVec N) × DescriptorType × FaultRecord × Bool × (BitVec 2) × TTWState)
                  )
                (pure ((aligned, descaddress, descriptor, desctype, fault, s1aarch64, s2fs1mro, skl, walkaddress, walkstate)))
            (pure loop_vars) ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
            (Bool × FullAddress × (BitVec N) × DescriptorType × FaultRecord × Bool × Bool × (BitVec 2) × AddressDescriptor × TTWState)
            )
          let oa ← (( do (StageOA va walkparams.d128 walkparams.tgx walkstate) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FullAddress )
          let w__63 ← (( do
            if (((walkstate.contiguous == 1#1) : Bool) : Bool)
            then
              (do
                (AArch64_ContiguousBitFaults walkparams.d128 walkparams.txsz walkparams.tgx
                  walkstate.level))
            else (pure false) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
          let fault ← (( do
            if (w__63 : Bool)
            then
              (let fault : FaultRecord := { fault with statuscode := Fault_Translation }
              (pure (fault)))
            else
              (do
                let w__65 ← (( do
                  if ((((BEq.beq desctype DescriptorType_Leaf) && (walkstate.level <b FINAL_LEVEL)) : Bool) : Bool)
                  then
                    (do
                      (AArch64_BlocknTFaults walkparams.d128 descriptor))
                  else (pure false) ) : SailME
                  (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                if (w__65 : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                  (pure (fault)))
                else
                  (do
                    ArmFull.assert ((N == 64) || (N == 128)) "sail-arm/v8_base.sail:27521.42-27521.43"
                    let w__66 ← (( do
                      (AArch64_S1AMECFault walkparams walkstate.baseaddress.paspace regime
                        descriptor) ) : SailME
                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                    if (w__66 : Bool)
                    then
                      (let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                      (pure (fault)))
                    else
                      (do
                        let w__67 ← (( do
                          (AArch64_OAOutOfRange oa.address walkparams.d128 walkparams.ps
                            walkparams.tgx) ) : SailME
                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                        if (w__67 : Bool)
                        then
                          (let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
                          (pure (fault)))
                        else
                          (do
                            let w__70 ← (( do
                              if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)])) == 0#1) && (walkparams.ha == 0#1)) : Bool) : Bool)
                              then
                                (do
                                  let w__69 ← (( do
                                    if ((((BEq.beq accdesc.acctype AccessType_DC) || (BEq.beq
                                           accdesc.acctype AccessType_IC)) : Bool) : Bool)
                                    then
                                      (do
                                        let w__68 ← (( do
                                          (__IMPDEF_boolean
                                            "Generate access flag fault on IC/DC operations") ) :
                                          SailME
                                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                          Bool )
                                        (pure (((! w__68) : Bool))))
                                    else (pure false) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    Bool )
                                  (pure (((! w__69) : Bool))))
                              else (pure false) ) : SailME
                              (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                            let fault : FaultRecord :=
                              if (w__70 : Bool)
                              then { fault with statuscode := Fault_AccessFlag }
                              else fault
                            (pure (fault)))))) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FaultRecord )
          if ((bne fault.statuscode Fault_None) : Bool)
          then
            (do
              let w__71 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
              let w__72 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
              let w__73 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
              (pure ((fault, w__71, w__72, w__73))))
          else
            (do
              let w__76 ← (( do
                (pure ((← do
                      (pure ((← do
                            readReg __tlb_enabled) && ((BEq.beq fault.statuscode Fault_None) : Bool)))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 10)])) == 1#1) : Bool))) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
              if (w__76 : Bool)
              then
                (do
                  let tlbcontext : TLBContext := { tlbcontext with xs := walkstate.memattrs.xs }
                  let tlbcontext : TLBContext := { tlbcontext with level := walkstate.level }
                  let tlbcontext : TLBContext := { tlbcontext with nG := walkstate.nG }
                  let tlbcontext : TLBContext :=
                    { tlbcontext with isd128 := (walkparams.d128 == 1#1) }
                  let tlbrecord : TLBRecord := { tlbrecord with context := tlbcontext }
                  let tlbrecord : TLBRecord := { tlbrecord with walkstate := walkstate }
                  let tlbrecord : TLBRecord :=
                    { tlbrecord with blocksize := (TranslationSize walkparams.d128 walkparams.tgx
                        walkstate.level) }
                  let tlbrecord ← (( do
                    if ((walkparams.d128 == 1#1) : Bool)
                    then
                      (do
                        ArmFull.assert (127 <b N) "sail-arm/v8_base.sail:27542.39-27542.40"
                        let tlbrecord : TLBRecord :=
                          { tlbrecord with s1descriptor := (Sail.BitVec.extractLsb descriptor 127 0) }
                        (pure (tlbrecord)))
                    else
                      (do
                        ArmFull.assert (63 <b N) "sail-arm/v8_base.sail:27545.38-27545.39"
                        let tlbrecord : TLBRecord :=
                          { tlbrecord with s1descriptor := (Sail.BitVec.updateSubrange
                              tlbrecord.s1descriptor 63 0 (Sail.BitVec.extractLsb descriptor 63 0)) }
                        let tlbrecord : TLBRecord :=
                          { tlbrecord with s1descriptor := (Sail.BitVec.updateSubrange
                              tlbrecord.s1descriptor 127 64 (Zeros (n := 64))) }
                        (pure (tlbrecord))) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
                  let tlbrecord ← (( do
                    if ((walkstate.contiguous == 1#1) : Bool)
                    then
                      (do
                        let w__77 ← (( do
                          (ContiguousSize walkparams.d128 walkparams.tgx walkstate.level) ) : SailME
                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Int )
                        let tlbrecord := ({ tlbrecord with contigsize := w__77 } : TLBRecord)
                        (pure (tlbrecord)))
                    else
                      (let tlbrecord : TLBRecord := { tlbrecord with contigsize := 0 }
                      (pure (tlbrecord))) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
                  (pure ((S1TLBCache tlbrecord))))
              else (pure (()))
              (pure ((fault, walkaddress, walkstate, descriptor))))))


end ArmFull.Functions
