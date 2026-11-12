import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0022
import ArmFull.Fn.M0038
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0123
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0152
import ArmFull.Fn.M0154
import ArmFull.Fn.M0158
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0174
import ArmFull.Fn.M0179
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0212
import ArmFull.Fn.M0213
import ArmFull.Fn.M0219
import ArmFull.Fn.M0237
import ArmFull.Fn.M0247
import ArmFull.Fn.M0253
import ArmFull.Fn.M0258
import ArmFull.Fn.M0259

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

def CheckStreamingSVEEnabled (_ : Unit) : SailM Unit := do
  (CheckSMEEnabled ())
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.SM == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (SMEAccessTrap SMEExceptionType_NotStreaming w__1.EL))
  else (pure (()))


def CheckSMEAndZAEnabled (_ : Unit) : SailM Unit := do
  (CheckSMEEnabled ())
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.ZA == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (SMEAccessTrap SMEExceptionType_InactiveZA w__1.EL))
  else (pure (()))


def AArch64_CheckFPEnabled (_ : Unit) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        let w__3 ← (( do (IsInHost ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let disabled ← (( do (undefined_bool_at (← occLabel 2417) ()) ) : SailM Bool )
      let w__5 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
      let b__0 := (_get_CPACR_EL1_Type_FPEN w__5)
      let disabled ← (( do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
        then (pure (true))
        else
          (do
            match b__0 with
            | 0b01 =>
              (do
                let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                let disabled := ((w__6.EL == EL0) : Bool)
                (pure (disabled)))
            | _ => (pure (false))) ) : SailM Bool )
      let disabled := disabled
      if (disabled : Bool)
      then
        (do
          (AArch64_AdvSIMDFPAccessTrap EL1))
      else (pure (())))
  else (pure (()))
  (AArch64_CheckFPAdvSIMDTrap ())


def AArch32_S1WalkLD (fault_in : FaultRecord) (regime : Regime) (walkparams : S1TTWParams) (accdesc : AccessDescriptor) (va : (BitVec 32)) : SailM (FaultRecord × TTWState) := SailME.run do
  let finalwalkstate ← (( do (undefined_TTWState (← occLabel 2554) ()) ) : SailME
    (FaultRecord × TTWState) TTWState )
  let s2aligned ← (( do (undefined_bool_at (← occLabel 2555) ()) ) : SailME
    (FaultRecord × TTWState) Bool )
  let s2fault ← (( do (undefined_FaultRecord (← occLabel 2556) ()) ) : SailME
    (FaultRecord × TTWState) FaultRecord )
  let s2walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 2557) ()) ) : SailME
    (FaultRecord × TTWState) AddressDescriptor )
  let fault : FaultRecord := fault_in
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2558) ()) ) : SailME
    (FaultRecord × TTWState) TLBContext )
  let w__0 ← (( do readReg __tlb_enabled ) : SailME (FaultRecord × TTWState) Bool )
  let (fault, tlbcontext) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (AArch32_GetS1TLBContext regime accdesc.ss va) ) : SailME
          (FaultRecord × TTWState) TLBContext )
        let tlbcontext := (w__1 : TLBContext)
        let tlbentry ← (( do (S1TLBLookup tlbcontext) ) : SailME (FaultRecord × TTWState) TLBLine
          )
        let fault ← (( do
          if (tlbentry.valid_name : Bool)
          then
            (do
              let finalwalkstate : TTWState := tlbentry.tlbrecord.walkstate
              let fault : FaultRecord := { fault with level := finalwalkstate.level }
              SailME.throw ((fault, finalwalkstate) : (FaultRecord × TTWState))
              (pure (fault)))
          else (pure (fault)) ) : SailME (FaultRecord × TTWState) FaultRecord )
        (pure ((fault, tlbcontext))))
    else (pure ((fault, tlbcontext))) ) : SailME (FaultRecord × TTWState)
    (FaultRecord × TLBContext) )
  let txsz ← (( do (undefined_bitvector_at (← occLabel 2559) 3) ) : SailME
    (FaultRecord × TTWState) (BitVec 3) )
  let ttbr ← (( do (undefined_bitvector_at (← occLabel 2560) 64) ) : SailME
    (FaultRecord × TTWState) (BitVec 64) )
  let epd ← (( do (undefined_bitvector_at (← occLabel 2561) 1) ) : SailME
    (FaultRecord × TTWState) (BitVec 1) )
  let varange ← (( do (undefined_VARange (← occLabel 2562) ()) ) : SailME
    (FaultRecord × TTWState) VARange )
  let (epd, ttbr, txsz, varange) ← (( do
    if ((BEq.beq regime Regime_EL2) : Bool)
    then
      (do
        let w__2 ← (( do readReg HTTBR ) : SailME (FaultRecord × TTWState) (BitVec 64) )
        let ttbr := (w__2 : (BitVec 64))
        let txsz : (BitVec 3) := walkparams.t0sz
        let varange : VARange := VARange_LOWER
        (pure ((epd, ttbr, txsz, varange))))
    else
      (do
        let w__3 ← (( do (AArch32_GetVARange va walkparams.t0sz walkparams.t1sz) ) : SailME
          (FaultRecord × TTWState) VARange )
        let varange := (w__3 : VARange)
        let ttbr0 ← (( do (undefined_bitvector_at (← occLabel 2563) 64) ) : SailME
          (FaultRecord × TTWState) (BitVec 64) )
        let ttbr1 ← (( do (undefined_bitvector_at (← occLabel 2564) 64) ) : SailME
          (FaultRecord × TTWState) (BitVec 64) )
        let ttbcr ← (( do (undefined_TTBCR_Type (← occLabel 2565) ()) ) : SailME
          (FaultRecord × TTWState) TTBCR_Type )
        let (ttbcr, ttbr0, ttbr1) ← (( do
          if ((BEq.beq regime Regime_EL30) : Bool)
          then
            (do
              let w__4 ← (( do readReg TTBCR_S ) : SailME (FaultRecord × TTWState) (BitVec 32) )
              let ttbcr := (w__4 : (BitVec 32))
              let w__5 ← (( do readReg TTBR0_S ) : SailME (FaultRecord × TTWState) (BitVec 64) )
              let ttbr0 := (w__5 : (BitVec 64))
              let w__6 ← (( do readReg TTBR1_S ) : SailME (FaultRecord × TTWState) (BitVec 64) )
              let ttbr1 := (w__6 : (BitVec 64))
              (pure ((ttbcr, ttbr0, ttbr1))))
          else
            (do
              if ((HaveAArch32EL EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (TTBCR_NS_read ()) ) : SailME (FaultRecord × TTWState)
                    (BitVec 32) )
                  let ttbcr := (w__7 : (BitVec 32))
                  let w__8 ← (( do readReg TTBR0_NS ) : SailME (FaultRecord × TTWState)
                    (BitVec 64) )
                  let ttbr0 := (w__8 : (BitVec 64))
                  let w__9 ← (( do readReg TTBR1_NS ) : SailME (FaultRecord × TTWState)
                    (BitVec 64) )
                  let ttbr1 := (w__9 : (BitVec 64))
                  (pure ((ttbcr, ttbr0, ttbr1))))
              else
                (do
                  let w__10 ← (( do (TTBCR_read ()) ) : SailME (FaultRecord × TTWState)
                    (BitVec 32) )
                  let ttbcr := (w__10 : (BitVec 32))
                  let w__11 ← (( do (TTBR0_read ()) ) : SailME (FaultRecord × TTWState)
                    (BitVec 64) )
                  let ttbr0 := (w__11 : (BitVec 64))
                  let w__12 ← (( do (TTBR1_read ()) ) : SailME (FaultRecord × TTWState)
                    (BitVec 64) )
                  let ttbr1 := (w__12 : (BitVec 64))
                  (pure ((ttbcr, ttbr0, ttbr1))))) ) : SailME (FaultRecord × TTWState)
          ((BitVec 32) × (BitVec 64) × (BitVec 64)) )
        ArmFull.assert ((_get_TTBCR_Type_EAE ttbcr) == 1#1) "sail-arm/v8_base.sail:38080.32-38080.33"
        let (epd, ttbr, txsz) : ((BitVec 1) × (BitVec 64) × (BitVec 3)) :=
          if ((BEq.beq varange VARange_LOWER) : Bool)
          then
            (let txsz : (BitVec 3) := walkparams.t0sz
            let ttbr : (BitVec 64) := ttbr0
            let epd : (BitVec 1) := (_get_TTBCR_Type_EPD0 ttbcr)
            (epd, ttbr, txsz))
          else
            (let txsz : (BitVec 3) := walkparams.t1sz
            let ttbr : (BitVec 64) := ttbr1
            let epd : (BitVec 1) := (_get_TTBCR_Type_EPD1 ttbcr)
            (epd, ttbr, txsz))
        (pure ((epd, ttbr, txsz, varange)))) ) : SailME (FaultRecord × TTWState)
    ((BitVec 1) × (BitVec 64) × (BitVec 3) × VARange) )
  if (((bne regime Regime_EL2) && (epd == 1#1)) : Bool)
  then
    (do
      let fault : FaultRecord := { fault with level := 1 }
      let fault : FaultRecord := { fault with statuscode := Fault_Translation }
      let w__13 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState) TTWState )
      (pure ((fault, w__13))))
  else
    (do
      let iasize : Int := (AArch32_S1IASize txsz)
      let granulebits : Int := (TGxGranuleBits walkparams.tgx)
      let stride : Int := (granulebits -i 3)
      let startlevel : Int := (FINAL_LEVEL -i (fdiv_int ((iasize -i 1) -i granulebits) stride))
      let levels : Int := (FINAL_LEVEL -i startlevel)
      if ((! (IsZero (Sail.BitVec.extractLsb ttbr 47 40))) : Bool)
      then
        (do
          let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
          let fault : FaultRecord := { fault with level := 0 }
          let w__14 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState) TTWState
            )
          (pure ((fault, w__14))))
      else
        (do
          let baseaddress ← (( do (undefined_FullAddress (← occLabel 2566) ()) ) : SailME
            (FaultRecord × TTWState) FullAddress )
          let baselsb : Int := ((iasize -i ((levels *i stride) +i granulebits)) +i 3)
          let baseaddress : FullAddress :=
            { baseaddress with paspace := if ((BEq.beq accdesc.ss SS_Secure) : Bool)
              then PAS_Secure
              else PAS_NonSecure }
          ArmFull.assert ((0 ≤b baselsb) && (baselsb ≤b 39)) "sail-arm/v8_base.sail:38110.55-38110.56"
          let baseaddress : FullAddress :=
            { baseaddress with address := (Sail.BitVec.zeroExtend
                ((Sail.BitVec.extractLsb ttbr 39 (Sail.Int.toNatChecked (baselsb))) +++ (Zeros
                    (n := (Sail.Int.toNatChecked (baselsb))))) 56) }
          let walkstate ← (( do (undefined_TTWState (← occLabel 2567) ()) ) : SailME
            (FaultRecord × TTWState) TTWState )
          let walkstate : TTWState := { walkstate with baseaddress := baseaddress }
          let walkstate : TTWState := { walkstate with level := startlevel }
          let walkstate : TTWState := { walkstate with istable := true }
          let walkstate : TTWState :=
            { walkstate with nG := if ((HasUnprivileged regime) : Bool)
              then 1#1
              else 0#1 }
          let w__15 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) :
            SailME (FaultRecord × TTWState) MemoryAttributes )
          let walkstate := ({ walkstate with memattrs := w__15 } : TTWState)
          let walkstate : TTWState :=
            { walkstate with permissions := { walkstate.permissions with ap_table := 0b00#2 } }
          let walkstate : TTWState :=
            { walkstate with permissions := { walkstate.permissions with xn_table := 0#1 } }
          let walkstate : TTWState :=
            { walkstate with permissions := { walkstate.permissions with pxn_table := 0#1 } }
          let indexmsb : Int := (iasize -i 1)
          let descriptor ← (( do (undefined_bitvector_at (← occLabel 2568) 64) ) : SailME
            (FaultRecord × TTWState) (BitVec 64) )
          let walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 2569) ()) ) : SailME
            (FaultRecord × TTWState) AddressDescriptor )
          let walkaddress : AddressDescriptor :=
            { walkaddress with vaddress := (Sail.BitVec.zeroExtend va 64) }
          let w__16 ← (( do (AArch32_S1DCacheEnabled regime) ) : SailME (FaultRecord × TTWState)
            Bool )
          let walkaddress ← (( do
            if ((! w__16) : Bool)
            then
              (do
                let w__17 ← (( do (NormalNCMemAttr ()) ) : SailME (FaultRecord × TTWState)
                  MemoryAttributes )
                let walkaddress := ({ walkaddress with memattrs := w__17 } : AddressDescriptor)
                let walkaddress : AddressDescriptor :=
                  { walkaddress with memattrs := { walkaddress.memattrs with xs := walkstate.memattrs.xs } }
                (pure (walkaddress)))
            else
              (let walkaddress : AddressDescriptor :=
                { walkaddress with memattrs := walkstate.memattrs }
              (pure (walkaddress))) ) : SailME (FaultRecord × TTWState) AddressDescriptor )
          let w__26 ← (( do
            if ((← do
                 if ((← do
                      if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                      then
                        (do
                          (AArch32_EL2Enabled accdesc.ss))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__20 ← (( do (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) )
                       : SailME (FaultRecord × TTWState) Bool )
                     let w__23 ← (( do
                       if (w__20 : Bool)
                       then
                         (do
                           let w__21 ← (( do (HCR_read ()) ) : SailME (FaultRecord × TTWState)
                             (BitVec 32) )
                           (pure ((_get_HCR_Type_VM w__21))))
                       else
                         (do
                           let w__22 ← (( do readReg HCR_EL2 ) : SailME (FaultRecord × TTWState)
                             (BitVec 64) )
                           (pure ((_get_HCR_EL2_Type_VM w__22)))) ) : SailME
                       (FaultRecord × TTWState) (BitVec 1) )
                     (pure (((w__23 == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__25 ← (( do (__IMPDEF_boolean "Apply effective shareability at stage 1") ) :
                  SailME (FaultRecord × TTWState) Bool )
                (pure (((! w__25) : Bool))))
            else (pure false) ) : SailME (FaultRecord × TTWState) Bool )
          let walkaddress : AddressDescriptor :=
            if (w__26 : Bool)
            then
              { walkaddress with memattrs := { walkaddress.memattrs with shareability := walkstate.memattrs.shareability } }
            else
              { walkaddress with memattrs := { walkaddress.memattrs with shareability := (EffectiveShareability
                    walkaddress.memattrs) } }
          let indexlsb ← (( do (undefined_int_at (← occLabel 2570) ()) ) : SailME
            (FaultRecord × TTWState) Int )
          let desctype ← (( do (undefined_DescriptorType (← occLabel 2571) ()) ) : SailME
            (FaultRecord × TTWState) DescriptorType )
          let (descriptor, desctype, fault, indexlsb, indexmsb, s2aligned, s2fault, s2walkaddress, walkaddress, walkstate) ← (( do
            let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (descriptor, desctype, fault, indexlsb, indexmsb, s2aligned, s2fault, s2walkaddress, walkaddress, walkstate) => (pure (BEq.beq
                desctype DescriptorType_Leaf))) (descriptor, desctype, fault, indexlsb, indexmsb, s2aligned, s2fault, s2walkaddress, walkaddress, walkstate)
              fun (descriptor, desctype, fault, indexlsb, indexmsb, s2aligned, s2fault, s2walkaddress, walkaddress, walkstate) => do
                let fault : FaultRecord := { fault with level := walkstate.level }
                let indexlsb : Int := (((FINAL_LEVEL -i walkstate.level) *i stride) +i granulebits)
                let indexmsb : Int := indexmsb
                let indexlsb : Int := indexlsb
                ArmFull.assert ((0 ≤b indexlsb) && ((indexlsb ≤b indexmsb) && (indexmsb <b 32))) "sail-arm/v8_base.sail:38147.91-38147.92"
                let index : (BitVec 40) :=
                  (Sail.BitVec.zeroExtend
                    ((Sail.BitVec.extractLsb va (Sail.Int.toNatChecked (indexmsb))
                        (Sail.Int.toNatChecked (indexlsb))) +++ 0b000#3) 40)
                let walkaddress : AddressDescriptor :=
                  { walkaddress with paddress := { walkaddress.paddress with address := (walkstate.baseaddress.address ||| (Sail.BitVec.castWidth (m := 56) (Sail.BitVec.zeroExtend
                          index 56))) } }
                let walkaddress : AddressDescriptor :=
                  { walkaddress with paddress := { walkaddress.paddress with paspace := walkstate.baseaddress.paspace } }
                let toplevel : Bool := (walkstate.level == startlevel)
                let walkaccess ← (( do (CreateAccDescS1TTW toplevel varange accdesc) ) : SailME
                  (FaultRecord × TTWState) AccessDescriptor )
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
                let w__28 ← (( do
                  if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                  then
                    (do
                      (AArch32_EL2Enabled accdesc.ss))
                  else (pure false) ) : SailME (FaultRecord × TTWState) Bool )
                let (descriptor, fault, s2aligned, s2fault, s2walkaddress) ← (( do
                  if (w__28 : Bool)
                  then
                    (do
                      let s2aligned : Bool := true
                      let w__29 ← (( do
                        (AArch32_S2Translate fault walkaddress (some walkstate.level) s2aligned
                          walkaccess) ) : SailME (FaultRecord × TTWState)
                        (FaultRecord × AddressDescriptor) )
                      let (tup__0, tup__1) := (w__29 : (FaultRecord × AddressDescriptor))
                      let s2fault : FaultRecord := tup__0
                      let s2walkaddress : AddressDescriptor := tup__1
                      let (descriptor, fault) ← (( do
                        if ((bne s2fault.statuscode Fault_None) : Bool)
                        then
                          (do
                            let w__30 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                              (FaultRecord × TTWState) TTWState )
                            SailME.throw ((s2fault, w__30) : (FaultRecord × TTWState))
                            (pure ((descriptor, fault))))
                        else
                          (do
                            let w__31 ← (( do
                              (FetchDescriptor walkparams.ee s2walkaddress walkaccess fault 64
                                translation_info) ) : SailME (FaultRecord × TTWState)
                              (FaultRecord × (BitVec 64)) )
                            let (tup__0, tup__1) := (w__31 : (FaultRecord × (BitVec 64)))
                            let fault : FaultRecord := tup__0
                            let descriptor : (BitVec 64) := tup__1
                            (pure ((descriptor, fault)))) ) : SailME (FaultRecord × TTWState)
                        ((BitVec 64) × FaultRecord) )
                      (pure ((descriptor, fault, s2aligned, s2fault, s2walkaddress))))
                  else
                    (do
                      let w__32 ← (( do
                        (FetchDescriptor walkparams.ee walkaddress walkaccess fault 64
                          translation_info) ) : SailME (FaultRecord × TTWState)
                        (FaultRecord × (BitVec 64)) )
                      let (tup__0, tup__1) := (w__32 : (FaultRecord × (BitVec 64)))
                      let fault : FaultRecord := tup__0
                      let descriptor : (BitVec 64) := tup__1
                      (pure ((descriptor, fault, s2aligned, s2fault, s2walkaddress)))) ) : SailME
                  (FaultRecord × TTWState)
                  ((BitVec 64) × FaultRecord × Bool × FaultRecord × AddressDescriptor) )
                let (desctype, fault, indexmsb, walkstate) ← (( do
                  if ((bne fault.statuscode Fault_None) : Bool)
                  then
                    (do
                      let w__33 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                        (FaultRecord × TTWState) TTWState )
                      SailME.throw ((fault, w__33) : (FaultRecord × TTWState))
                      (pure ((desctype, fault, indexmsb, walkstate))))
                  else
                    (do
                      let desctype : DescriptorType :=
                        (AArch32_DecodeDescriptorTypeLD descriptor walkstate.level)
                      let (fault, indexmsb, walkstate) ← (( do
                        match desctype with
                        | .DescriptorType_Table =>
                          (do
                            if ((! (IsZero (Sail.BitVec.extractLsb descriptor 47 40))) : Bool)
                            then
                              (do
                                let fault : FaultRecord :=
                                  { fault with statuscode := Fault_AddressSize }
                                let w__34 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                  (FaultRecord × TTWState) TTWState )
                                SailME.throw ((fault, w__34) : (FaultRecord × TTWState))
                                (pure ((fault, indexmsb, walkstate))))
                            else
                              (let walkstate : TTWState :=
                                { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                                      ((Sail.BitVec.extractLsb descriptor 39 12) +++ (Zeros
                                          (n := 12))) 56) } }
                              let walkstate : TTWState :=
                                if (((BEq.beq walkstate.baseaddress.paspace PAS_Secure) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           descriptor 63)])) == 1#1)) : Bool)
                                then
                                  { walkstate with baseaddress := { walkstate.baseaddress with paspace := PAS_NonSecure } }
                                else walkstate
                              let walkstate : TTWState :=
                                if ((walkparams.hpd == 0#1) : Bool)
                                then
                                  (let walkstate : TTWState :=
                                    { walkstate with permissions := { walkstate.permissions with xn_table := (walkstate.permissions.xn_table ||| (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                              descriptor 60)]))) } }
                                  let walkstate : TTWState :=
                                    { walkstate with permissions := { walkstate.permissions with ap_table := (walkstate.permissions.ap_table ||| (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                            descriptor 62 61))) } }
                                  { walkstate with permissions := { walkstate.permissions with pxn_table := (walkstate.permissions.pxn_table ||| (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                            descriptor 59)]))) } })
                                else walkstate
                              let walkstate : TTWState :=
                                { walkstate with level := (walkstate.level +i 1) }
                              let indexmsb : Int := (indexlsb -i 1)
                              (pure ((fault, indexmsb, walkstate)))))
                        | .DescriptorType_Invalid =>
                          (do
                            let fault : FaultRecord :=
                              { fault with statuscode := Fault_Translation }
                            let w__35 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                              (FaultRecord × TTWState) TTWState )
                            SailME.throw ((fault, w__35) : (FaultRecord × TTWState))
                            (pure ((fault, indexmsb, walkstate))))
                        | .DescriptorType_Leaf =>
                          (let walkstate : TTWState := { walkstate with istable := false }
                          (pure ((fault, indexmsb, walkstate)))) ) : SailME
                        (FaultRecord × TTWState) (FaultRecord × Int × TTWState) )
                      (pure ((desctype, fault, indexmsb, walkstate)))) ) : SailME
                  (FaultRecord × TTWState) (DescriptorType × FaultRecord × Int × TTWState) )
                (pure ((descriptor, desctype, fault, indexlsb, indexmsb, s2aligned, s2fault, s2walkaddress, walkaddress, walkstate)))
            (pure loop_vars) ) : SailME (FaultRecord × TTWState)
            ((BitVec 64) × DescriptorType × FaultRecord × Int × Int × Bool × FaultRecord × AddressDescriptor × AddressDescriptor × TTWState)
            )
          let indexlsb : Int := indexlsb
          if ((! (IsZero (Sail.BitVec.extractLsb descriptor 47 40))) : Bool)
          then
            (do
              let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
              let w__36 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState)
                TTWState )
              (pure ((fault, w__36))))
          else
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)])) == 0#1) : Bool)
              then
                (do
                  let fault : FaultRecord := { fault with statuscode := Fault_AccessFlag }
                  let w__37 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState)
                    TTWState )
                  (pure ((fault, w__37))))
              else
                (do
                  let walkstate : TTWState :=
                    { walkstate with permissions := { walkstate.permissions with xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                            descriptor 54)])) } }
                  let walkstate : TTWState :=
                    { walkstate with permissions := { walkstate.permissions with pxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                            descriptor 53)])) } }
                  let walkstate : TTWState :=
                    { walkstate with permissions := { walkstate.permissions with ap := ((Sail.BitVec.extractLsb
                            descriptor 7 6) +++ 1#1) } }
                  let walkstate : TTWState :=
                    { walkstate with contiguous := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 52)])) }
                  let walkstate : TTWState :=
                    if ((BEq.beq regime Regime_EL2) : Bool)
                    then { walkstate with nG := 0#1 }
                    else
                      (if (((BEq.beq accdesc.ss SS_Secure) && (BEq.beq walkstate.baseaddress.paspace
                             PAS_NonSecure)) : Bool)
                      then { walkstate with nG := 1#1 }
                      else
                        { walkstate with nG := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              descriptor 11)])) })
                  ArmFull.assert ((0 ≤b indexlsb) && (indexlsb ≤b 39)) "sail-arm/v8_base.sail:38226.57-38226.58"
                  let walkstate : TTWState :=
                    { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                          ((Sail.BitVec.extractLsb descriptor 39 (Sail.Int.toNatChecked (indexlsb))) +++ (Zeros
                              (n := (Sail.Int.toNatChecked (indexlsb))))) 56) } }
                  let walkstate : TTWState :=
                    if (((BEq.beq walkstate.baseaddress.paspace PAS_Secure) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               descriptor 5)])) == 1#1)) : Bool)
                    then
                      { walkstate with baseaddress := { walkstate.baseaddress with paspace := PAS_NonSecure } }
                    else walkstate
                  let memattr : (BitVec 3) := (Sail.BitVec.extractLsb descriptor 4 2)
                  let sh : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 9 8)
                  let attr ← (( do (AArch32_MAIRAttr (BitVec.toNat memattr) walkparams.mair) ) :
                    SailME (FaultRecord × TTWState) (BitVec 8) )
                  let s1aarch64 : Bool := false
                  let w__38 ← (( do (S1DecodeMemAttrs attr sh s1aarch64 walkparams) ) : SailME
                    (FaultRecord × TTWState) MemoryAttributes )
                  let walkstate := ({ walkstate with memattrs := w__38 } : TTWState)
                  let w__39 ← (( do readReg __tlb_enabled ) : SailME (FaultRecord × TTWState)
                    Bool )
                  if (w__39 : Bool)
                  then
                    (do
                      let tlbcontext : TLBContext := { tlbcontext with xs := walkstate.memattrs.xs }
                      let tlbcontext : TLBContext := { tlbcontext with level := walkstate.level }
                      let tlbcontext : TLBContext := { tlbcontext with nG := walkstate.nG }
                      let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 2572) ()) ) :
                        SailME (FaultRecord × TTWState) TLBRecord )
                      let tlbrecord : TLBRecord := { tlbrecord with context := tlbcontext }
                      let tlbrecord : TLBRecord := { tlbrecord with walkstate := walkstate }
                      let tlbrecord : TLBRecord :=
                        { tlbrecord with blocksize := (TranslationSize walkparams.d128
                            walkparams.tgx walkstate.level) }
                      let tlbrecord ← (( do
                        if ((walkstate.contiguous == 1#1) : Bool)
                        then
                          (do
                            let w__40 ← (( do
                              (ContiguousSize walkparams.d128 walkparams.tgx walkstate.level) ) :
                              SailME (FaultRecord × TTWState) Int )
                            let tlbrecord := ({ tlbrecord with contigsize := w__40 } : TLBRecord)
                            (pure (tlbrecord)))
                        else
                          (let tlbrecord : TLBRecord := { tlbrecord with contigsize := 0 }
                          (pure (tlbrecord))) ) : SailME (FaultRecord × TTWState) TLBRecord )
                      (pure ((S1TLBCache tlbrecord))))
                  else (pure (()))
                  (pure ((fault, walkstate)))))))


def AArch32_S1WalkSD (fault_in : FaultRecord) (regime : Regime) (accdesc : AccessDescriptor) (va : (BitVec 32)) : SailM (FaultRecord × TTWState) := SailME.run do
  let finalwalkstate ← (( do (undefined_TTWState (← occLabel 2599) ()) ) : SailME
    (FaultRecord × TTWState) TTWState )
  let s2aligned ← (( do (undefined_bool_at (← occLabel 2600) ()) ) : SailME
    (FaultRecord × TTWState) Bool )
  let s2fault ← (( do (undefined_FaultRecord (← occLabel 2601) ()) ) : SailME
    (FaultRecord × TTWState) FaultRecord )
  let s2walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 2602) ()) ) : SailME
    (FaultRecord × TTWState) AddressDescriptor )
  let fault : FaultRecord := fault_in
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2603) ()) ) : SailME
    (FaultRecord × TTWState) TLBContext )
  let w__0 ← (( do readReg __tlb_enabled ) : SailME (FaultRecord × TTWState) Bool )
  let (fault, tlbcontext) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (AArch32_GetS1TLBContext regime accdesc.ss va) ) : SailME
          (FaultRecord × TTWState) TLBContext )
        let tlbcontext := (w__1 : TLBContext)
        let tlbentry ← (( do (S1TLBLookup tlbcontext) ) : SailME (FaultRecord × TTWState) TLBLine
          )
        let fault ← (( do
          if (tlbentry.valid_name : Bool)
          then
            (do
              let finalwalkstate : TTWState := tlbentry.tlbrecord.walkstate
              let fault : FaultRecord := { fault with level := finalwalkstate.level }
              SailME.throw ((fault, finalwalkstate) : (FaultRecord × TTWState))
              (pure (fault)))
          else (pure (fault)) ) : SailME (FaultRecord × TTWState) FaultRecord )
        (pure ((fault, tlbcontext))))
    else (pure ((fault, tlbcontext))) ) : SailME (FaultRecord × TTWState)
    (FaultRecord × TLBContext) )
  let sctlr ← (( do (undefined_SCTLR_Type (← occLabel 2604) ()) ) : SailME
    (FaultRecord × TTWState) SCTLR_Type )
  let ttbcr ← (( do (undefined_TTBCR_Type (← occLabel 2605) ()) ) : SailME
    (FaultRecord × TTWState) TTBCR_Type )
  let ttbr0 ← (( do (undefined_TTBR0_Type (← occLabel 2606) ()) ) : SailME
    (FaultRecord × TTWState) TTBR0_Type )
  let ttbr1 ← (( do (undefined_TTBR1_Type (← occLabel 2607) ()) ) : SailME
    (FaultRecord × TTWState) TTBR1_Type )
  let (sctlr, ttbcr, ttbr0, ttbr1) ← (( do
    if ((BEq.beq regime Regime_EL30) : Bool)
    then
      (do
        let w__2 ← (( do readReg SCTLR_S ) : SailME (FaultRecord × TTWState) (BitVec 32) )
        let sctlr := (w__2 : (BitVec 32))
        let w__3 ← (( do readReg TTBCR_S ) : SailME (FaultRecord × TTWState) (BitVec 32) )
        let ttbcr := (w__3 : (BitVec 32))
        let w__4 ← (( do readReg TTBR0_S ) : SailME (FaultRecord × TTWState) (BitVec 64) )
        let ttbr0 := (w__4 : (BitVec 64))
        let w__5 ← (( do readReg TTBR1_S ) : SailME (FaultRecord × TTWState) (BitVec 64) )
        let ttbr1 := (w__5 : (BitVec 64))
        (pure ((sctlr, ttbcr, ttbr0, ttbr1))))
    else
      (do
        if ((HaveAArch32EL EL3) : Bool)
        then
          (do
            let w__6 ← (( do (SCTLR_NS_read ()) ) : SailME (FaultRecord × TTWState) (BitVec 32) )
            let sctlr := (w__6 : (BitVec 32))
            let w__7 ← (( do (TTBCR_NS_read ()) ) : SailME (FaultRecord × TTWState) (BitVec 32) )
            let ttbcr := (w__7 : (BitVec 32))
            let w__8 ← (( do readReg TTBR0_NS ) : SailME (FaultRecord × TTWState) (BitVec 64) )
            let ttbr0 := (w__8 : (BitVec 64))
            let w__9 ← (( do readReg TTBR1_NS ) : SailME (FaultRecord × TTWState) (BitVec 64) )
            let ttbr1 := (w__9 : (BitVec 64))
            (pure ((sctlr, ttbcr, ttbr0, ttbr1))))
        else
          (do
            let w__10 ← (( do (SCTLR_read__2 ()) ) : SailME (FaultRecord × TTWState) (BitVec 32)
              )
            let sctlr := (w__10 : (BitVec 32))
            let w__11 ← (( do (TTBCR_read ()) ) : SailME (FaultRecord × TTWState) (BitVec 32) )
            let ttbcr := (w__11 : (BitVec 32))
            let w__12 ← (( do (TTBR0_read ()) ) : SailME (FaultRecord × TTWState) (BitVec 64) )
            let ttbr0 := (w__12 : (BitVec 64))
            let w__13 ← (( do (TTBR1_read ()) ) : SailME (FaultRecord × TTWState) (BitVec 64) )
            let ttbr1 := (w__13 : (BitVec 64))
            (pure ((sctlr, ttbcr, ttbr0, ttbr1))))) ) : SailME (FaultRecord × TTWState)
    ((BitVec 32) × (BitVec 32) × (BitVec 64) × (BitVec 64)) )
  ArmFull.assert ((_get_TTBCR_Type_EAE ttbcr) == 0#1) "sail-arm/v8_base.sail:38758.28-38758.29"
  let ee : (BitVec 1) := (_get_SCTLR_Type_EE sctlr)
  let afe : (BitVec 1) := (_get_SCTLR_Type_AFE sctlr)
  let tre : (BitVec 1) := (_get_SCTLR_Type_TRE sctlr)
  let n : Nat := (BitVec.toNat (_get_TTBCR_Type_N ttbcr))
  let ttb ← (( do (undefined_bitvector_at (← occLabel 2608) 32) ) : SailME
    (FaultRecord × TTWState) (BitVec 32) )
  let pd ← (( do (undefined_bitvector_at (← occLabel 2609) 1) ) : SailME
    (FaultRecord × TTWState) (BitVec 1) )
  let irgn ← (( do (undefined_bitvector_at (← occLabel 2610) 2) ) : SailME
    (FaultRecord × TTWState) (BitVec 2) )
  let rgn ← (( do (undefined_bitvector_at (← occLabel 2611) 2) ) : SailME
    (FaultRecord × TTWState) (BitVec 2) )
  let s ← (( do (undefined_bitvector_at (← occLabel 2612) 1) ) : SailME
    (FaultRecord × TTWState) (BitVec 1) )
  let nos ← (( do (undefined_bitvector_at (← occLabel 2613) 1) ) : SailME
    (FaultRecord × TTWState) (BitVec 1) )
  let varange ← (( do (undefined_VARange (← occLabel 2614) ()) ) : SailME
    (FaultRecord × TTWState) VARange )
  let (irgn, n, nos, pd, rgn, s, ttb, varange) : ((BitVec 2) × Nat × (BitVec 1) × (BitVec 1) × (BitVec 2) × (BitVec 1) × (BitVec 32) × VARange) :=
    if (((n == 0) || (is_zero_subrange va 31 (32 -i n))) : Bool)
    then
      (let ttb : (BitVec 32) := ((_get_TTBR0_Type_TTB0 ttbr0) +++ (Zeros (n := 7)))
      let pd : (BitVec 1) := (_get_TTBCR_Type_PD0 ttbcr)
      let irgn : (BitVec 2) := (_get_TTBR0_Type_IRGN ttbr0)
      let rgn : (BitVec 2) := (_get_TTBR0_Type_RGN ttbr0)
      let s : (BitVec 1) := (_get_TTBR0_Type_S ttbr0)
      let nos : (BitVec 1) := (_get_TTBR0_Type_NOS ttbr0)
      let varange : VARange := VARange_LOWER
      (irgn, n, nos, pd, rgn, s, ttb, varange))
    else
      (let n : Nat := 0
      let ttb : (BitVec 32) := ((_get_TTBR1_Type_TTB1 ttbr1) +++ (Zeros (n := 7)))
      let pd : (BitVec 1) := (_get_TTBCR_Type_PD1 ttbcr)
      let irgn : (BitVec 2) := (_get_TTBR1_Type_IRGN ttbr1)
      let rgn : (BitVec 2) := (_get_TTBR1_Type_RGN ttbr1)
      let s : (BitVec 1) := (_get_TTBR1_Type_S ttbr1)
      let nos : (BitVec 1) := (_get_TTBR1_Type_NOS ttbr1)
      let varange : VARange := VARange_UPPER
      (irgn, n, nos, pd, rgn, s, ttb, varange))
  let n : Int := n
  if ((pd == 1#1) : Bool)
  then
    (do
      let fault : FaultRecord := { fault with level := 1 }
      let fault : FaultRecord := { fault with statuscode := Fault_Translation }
      let w__14 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState) TTWState )
      (pure ((fault, w__14))))
  else
    (do
      let baseaddress ← (( do (undefined_FullAddress (← occLabel 2615) ()) ) : SailME
        (FaultRecord × TTWState) FullAddress )
      let baseaddress : FullAddress :=
        { baseaddress with paspace := if ((BEq.beq accdesc.ss SS_Secure) : Bool)
          then PAS_Secure
          else PAS_NonSecure }
      let baseaddress : FullAddress :=
        { baseaddress with address := (Sail.BitVec.zeroExtend
            ((Sail.BitVec.extractLsb ttb 31 (Sail.Int.toNatChecked ((14 -i n)))) +++ (Zeros
                (n := (Sail.Int.toNatChecked ((14 -i n)))))) 56) }
      let startlevel : Nat := 1
      let walkstate ← (( do (undefined_TTWState (← occLabel 2616) ()) ) : SailME
        (FaultRecord × TTWState) TTWState )
      let walkstate : TTWState := { walkstate with baseaddress := baseaddress }
      let walkstate : TTWState := { walkstate with nG := 1#1 }
      let w__15 ← (( do (WalkMemAttrs (s +++ nos) irgn rgn) ) : SailME (FaultRecord × TTWState)
        MemoryAttributes )
      let walkstate := ({ walkstate with memattrs := w__15 } : TTWState)
      let walkstate : TTWState := { walkstate with level := startlevel }
      let walkstate : TTWState := { walkstate with istable := true }
      let domain ← (( do (undefined_bitvector_at (← occLabel 2617) 4) ) : SailME
        (FaultRecord × TTWState) (BitVec 4) )
      let descriptor ← (( do (undefined_bitvector_at (← occLabel 2618) 32) ) : SailME
        (FaultRecord × TTWState) (BitVec 32) )
      let walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 2619) ()) ) : SailME
        (FaultRecord × TTWState) AddressDescriptor )
      let walkaddress : AddressDescriptor :=
        { walkaddress with vaddress := (Sail.BitVec.zeroExtend va 64) }
      let w__16 ← (( do (AArch32_S1DCacheEnabled regime) ) : SailME (FaultRecord × TTWState) Bool
        )
      let walkaddress ← (( do
        if ((! w__16) : Bool)
        then
          (do
            let w__17 ← (( do (NormalNCMemAttr ()) ) : SailME (FaultRecord × TTWState)
              MemoryAttributes )
            let walkaddress := ({ walkaddress with memattrs := w__17 } : AddressDescriptor)
            let walkaddress : AddressDescriptor :=
              { walkaddress with memattrs := { walkaddress.memattrs with xs := walkstate.memattrs.xs } }
            (pure (walkaddress)))
        else
          (let walkaddress : AddressDescriptor :=
            { walkaddress with memattrs := walkstate.memattrs }
          (pure (walkaddress))) ) : SailME (FaultRecord × TTWState) AddressDescriptor )
      let w__26 ← (( do
        if ((← do
             if ((← do
                  if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                  then
                    (do
                      (AArch32_EL2Enabled accdesc.ss))
                  else (pure false)) : Bool)
             then
               (do
                 let w__20 ← (( do (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) :
                   SailME (FaultRecord × TTWState) Bool )
                 let w__23 ← (( do
                   if (w__20 : Bool)
                   then
                     (do
                       let w__21 ← (( do (HCR_read ()) ) : SailME (FaultRecord × TTWState)
                         (BitVec 32) )
                       (pure ((_get_HCR_Type_VM w__21))))
                   else
                     (do
                       let w__22 ← (( do readReg HCR_EL2 ) : SailME (FaultRecord × TTWState)
                         (BitVec 64) )
                       (pure ((_get_HCR_EL2_Type_VM w__22)))) ) : SailME (FaultRecord × TTWState)
                   (BitVec 1) )
                 (pure (((w__23 == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__25 ← (( do (__IMPDEF_boolean "Apply effective shareability at stage 1") ) :
              SailME (FaultRecord × TTWState) Bool )
            (pure (((! w__25) : Bool))))
        else (pure false) ) : SailME (FaultRecord × TTWState) Bool )
      let walkaddress : AddressDescriptor :=
        if (w__26 : Bool)
        then
          { walkaddress with memattrs := { walkaddress.memattrs with shareability := walkstate.memattrs.shareability } }
        else
          { walkaddress with memattrs := { walkaddress.memattrs with shareability := (EffectiveShareability
                walkaddress.memattrs) } }
      let nG ← (( do (undefined_bitvector_at (← occLabel 2620) 1) ) : SailME
        (FaultRecord × TTWState) (BitVec 1) )
      let ns ← (( do (undefined_bitvector_at (← occLabel 2621) 1) ) : SailME
        (FaultRecord × TTWState) (BitVec 1) )
      let pxn ← (( do (undefined_bitvector_at (← occLabel 2622) 1) ) : SailME
        (FaultRecord × TTWState) (BitVec 1) )
      let ap ← (( do (undefined_bitvector_at (← occLabel 2623) 3) ) : SailME
        (FaultRecord × TTWState) (BitVec 3) )
      let tex ← (( do (undefined_bitvector_at (← occLabel 2624) 3) ) : SailME
        (FaultRecord × TTWState) (BitVec 3) )
      let c ← (( do (undefined_bitvector_at (← occLabel 2625) 1) ) : SailME
        (FaultRecord × TTWState) (BitVec 1) )
      let b ← (( do (undefined_bitvector_at (← occLabel 2626) 1) ) : SailME
        (FaultRecord × TTWState) (BitVec 1) )
      let xn ← (( do (undefined_bitvector_at (← occLabel 2627) 1) ) : SailME
        (FaultRecord × TTWState) (BitVec 1) )
      let (ap, b, c, descriptor, domain, fault, nG, ns, pxn, s, s2aligned, s2fault, s2walkaddress, tex, walkaddress, walkstate, xn) ← (( do
        let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (ap, b, c, descriptor, domain, fault, nG, ns, pxn, s, s2aligned, s2fault, s2walkaddress, tex, walkaddress, walkstate, xn) => (pure (bne
            walkstate.sdftype SDFType_Table))) (ap, b, c, descriptor, domain, fault, nG, ns, pxn, s, s2aligned, s2fault, s2walkaddress, tex, walkaddress, walkstate, xn)
          fun (ap, b, c, descriptor, domain, fault, nG, ns, pxn, s, s2aligned, s2fault, s2walkaddress, tex, walkaddress, walkstate, xn) => do
            let fault : FaultRecord := { fault with level := walkstate.level }
            let index ← (( do (undefined_bitvector_at (← occLabel 2629) 32) ) : SailME
              (FaultRecord × TTWState) (BitVec 32) )
            let index : (BitVec 32) :=
              if ((walkstate.level == 1) : Bool)
              then
                (Sail.BitVec.zeroExtend
                  ((Sail.BitVec.extractLsb va (Sail.Int.toNatChecked ((31 -i n))) 20) +++ 0b00#2) 32)
              else (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va 19 12) +++ 0b00#2) 32)
            let walkaddress : AddressDescriptor :=
              { walkaddress with paddress := { walkaddress.paddress with address := (walkstate.baseaddress.address ||| (Sail.BitVec.castWidth (m := 56) (Sail.BitVec.zeroExtend
                      index 56))) } }
            let walkaddress : AddressDescriptor :=
              { walkaddress with paddress := { walkaddress.paddress with paspace := walkstate.baseaddress.paspace } }
            let toplevel : Bool := (walkstate.level == startlevel)
            let walkaccess ← (( do (CreateAccDescS1TTW toplevel varange accdesc) ) : SailME
              (FaultRecord × TTWState) AccessDescriptor )
            let translation_info : TranslationInfo :=
              { regime := regime
                vmid := none
                asid := none
                va := walkaddress.vaddress
                s1level := (some walkstate.level)
                s2info := none
                s1params := none
                s2params := none
                memattrs := walkaddress.memattrs }
            let w__28 ← (( do
              if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
              then
                (do
                  (AArch32_EL2Enabled accdesc.ss))
              else (pure false) ) : SailME (FaultRecord × TTWState) Bool )
            let (descriptor, fault, s2aligned, s2fault, s2walkaddress) ← (( do
              if (w__28 : Bool)
              then
                (do
                  let s2aligned : Bool := true
                  let w__29 ← (( do
                    (AArch32_S2Translate fault walkaddress (some walkstate.level) s2aligned
                      walkaccess) ) : SailME (FaultRecord × TTWState)
                    (FaultRecord × AddressDescriptor) )
                  let (tup__0, tup__1) := (w__29 : (FaultRecord × AddressDescriptor))
                  let s2fault : FaultRecord := tup__0
                  let s2walkaddress : AddressDescriptor := tup__1
                  let (descriptor, fault) ← (( do
                    if ((bne s2fault.statuscode Fault_None) : Bool)
                    then
                      (do
                        let w__30 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                          (FaultRecord × TTWState) TTWState )
                        SailME.throw ((s2fault, w__30) : (FaultRecord × TTWState))
                        (pure ((descriptor, fault))))
                    else
                      (do
                        let w__31 ← (( do
                          (FetchDescriptor ee s2walkaddress walkaccess fault 32 translation_info) )
                          : SailME (FaultRecord × TTWState) (FaultRecord × (BitVec 32)) )
                        let (tup__0, tup__1) := (w__31 : (FaultRecord × (BitVec 32)))
                        let fault : FaultRecord := tup__0
                        let descriptor : (BitVec 32) := tup__1
                        (pure ((descriptor, fault)))) ) : SailME (FaultRecord × TTWState)
                    ((BitVec 32) × FaultRecord) )
                  (pure ((descriptor, fault, s2aligned, s2fault, s2walkaddress))))
              else
                (do
                  let w__32 ← (( do
                    (FetchDescriptor ee walkaddress walkaccess fault 32 translation_info) ) : SailME
                    (FaultRecord × TTWState) (FaultRecord × (BitVec 32)) )
                  let (tup__0, tup__1) := (w__32 : (FaultRecord × (BitVec 32)))
                  let fault : FaultRecord := tup__0
                  let descriptor : (BitVec 32) := tup__1
                  (pure ((descriptor, fault, s2aligned, s2fault, s2walkaddress)))) ) : SailME
              (FaultRecord × TTWState)
              ((BitVec 32) × FaultRecord × Bool × FaultRecord × AddressDescriptor) )
            let (ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn) ← (( do
              if ((bne fault.statuscode Fault_None) : Bool)
              then
                (do
                  let w__33 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState)
                    TTWState )
                  SailME.throw ((fault, w__33) : (FaultRecord × TTWState))
                  (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))
              else
                (do
                  let walkstate : TTWState :=
                    { walkstate with sdftype := (AArch32_DecodeDescriptorTypeSD descriptor
                        walkstate.level) }
                  match walkstate.sdftype with
                  | .SDFType_Invalid =>
                    (do
                      let fault : FaultRecord := { fault with domain := domain }
                      let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                      let w__34 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                        (FaultRecord × TTWState) TTWState )
                      SailME.throw ((fault, w__34) : (FaultRecord × TTWState))
                      (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))
                  | .SDFType_Table =>
                    (let domain : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 8 5)
                    let ns : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 3)]))
                    let pxn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 2)]))
                    let walkstate : TTWState :=
                      { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                            ((Sail.BitVec.extractLsb descriptor 31 10) +++ (Zeros (n := 10))) 56) } }
                    let walkstate : TTWState := { walkstate with level := 2 }
                    (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))
                  | .SDFType_SmallPage =>
                    (let nG : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)]))
                    let s : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)]))
                    let ap : (BitVec 3) :=
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 9)])) +++ (Sail.BitVec.extractLsb
                          descriptor 5 4))
                    let tex : (BitVec 3) := (Sail.BitVec.extractLsb descriptor 8 6)
                    let c : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 3)]))
                    let b : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 2)]))
                    let xn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 0)]))
                    let walkstate : TTWState :=
                      { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                            ((Sail.BitVec.extractLsb descriptor 31 12) +++ (Zeros (n := 12))) 56) } }
                    let walkstate : TTWState := { walkstate with istable := false }
                    (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))
                  | .SDFType_LargePage =>
                    (let xn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 15)]))
                    let tex : (BitVec 3) := (Sail.BitVec.extractLsb descriptor 14 12)
                    let nG : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)]))
                    let s : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)]))
                    let ap : (BitVec 3) :=
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 9)])) +++ (Sail.BitVec.extractLsb
                          descriptor 5 4))
                    let c : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 3)]))
                    let b : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 2)]))
                    let walkstate : TTWState :=
                      { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                            ((Sail.BitVec.extractLsb descriptor 31 16) +++ (Zeros (n := 16))) 56) } }
                    let walkstate : TTWState := { walkstate with istable := false }
                    (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))
                  | .SDFType_Section =>
                    (let ns : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 19)]))
                    let nG : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 17)]))
                    let s : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 16)]))
                    let ap : (BitVec 3) :=
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 15)])) +++ (Sail.BitVec.extractLsb
                          descriptor 11 10))
                    let tex : (BitVec 3) := (Sail.BitVec.extractLsb descriptor 14 12)
                    let domain : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 8 5)
                    let xn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 4)]))
                    let c : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 3)]))
                    let b : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 2)]))
                    let pxn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 0)]))
                    let walkstate : TTWState :=
                      { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                            ((Sail.BitVec.extractLsb descriptor 31 20) +++ (Zeros (n := 20))) 56) } }
                    let walkstate : TTWState := { walkstate with istable := false }
                    (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))
                  | .SDFType_Supersection =>
                    (let ns : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 19)]))
                    let nG : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 17)]))
                    let s : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 16)]))
                    let ap : (BitVec 3) :=
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 15)])) +++ (Sail.BitVec.extractLsb
                          descriptor 11 10))
                    let tex : (BitVec 3) := (Sail.BitVec.extractLsb descriptor 14 12)
                    let xn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 4)]))
                    let c : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 3)]))
                    let b : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 2)]))
                    let pxn : (BitVec 1) :=
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 0)]))
                    let domain : (BitVec 4) := 0b0000#4
                    let walkstate : TTWState :=
                      { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                            (((Sail.BitVec.extractLsb descriptor 8 5) +++ ((Sail.BitVec.extractLsb
                                    descriptor 23 20) +++ (Sail.BitVec.extractLsb descriptor 31 24))) +++ (Zeros
                                (n := 24))) 56) } }
                    let walkstate : TTWState := { walkstate with istable := false }
                    (pure ((ap, b, c, domain, fault, nG, ns, pxn, s, tex, walkstate, xn))))) ) :
              SailME (FaultRecord × TTWState)
              ((BitVec 3) × (BitVec 1) × (BitVec 1) × (BitVec 4) × FaultRecord × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 3) × TTWState × (BitVec 1))
              )
            (pure ((ap, b, c, descriptor, domain, fault, nG, ns, pxn, s, s2aligned, s2fault, s2walkaddress, tex, walkaddress, walkstate, xn)))
        (pure loop_vars) ) : SailME (FaultRecord × TTWState)
        ((BitVec 3) × (BitVec 1) × (BitVec 1) × (BitVec 32) × (BitVec 4) × FaultRecord × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × Bool × FaultRecord × AddressDescriptor × (BitVec 3) × AddressDescriptor × TTWState × (BitVec 1))
        )
      if (((afe == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ap 0)])) == 0#1)) : Bool)
      then
        (do
          let fault : FaultRecord := { fault with domain := domain }
          let fault : FaultRecord := { fault with statuscode := Fault_AccessFlag }
          let w__35 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState) TTWState
            )
          (pure ((fault, w__35))))
      else
        (do
          let walkstate ← (( do
            if ((tre == 1#1) : Bool)
            then
              (do
                let w__36 ← (( do (AArch32_RemappedTEXDecode regime tex c b s) ) : SailME
                  (FaultRecord × TTWState) MemoryAttributes )
                let walkstate := ({ walkstate with memattrs := w__36 } : TTWState)
                (pure (walkstate)))
            else
              (do
                let w__37 ← (( do (RemapRegsHaveResetValues ()) ) : SailME
                  (FaultRecord × TTWState) Bool )
                if (w__37 : Bool)
                then
                  (do
                    let w__38 ← (( do (AArch32_DefaultTEXDecode tex c b s) ) : SailME
                      (FaultRecord × TTWState) MemoryAttributes )
                    let walkstate := ({ walkstate with memattrs := w__38 } : TTWState)
                    (pure (walkstate)))
                else
                  (do
                    let w__39 ← (( do (__IMPDEF_MemoryAttributes "") ) : SailME
                      (FaultRecord × TTWState) MemoryAttributes )
                    let walkstate := ({ walkstate with memattrs := w__39 } : TTWState)
                    (pure (walkstate)))) ) : SailME (FaultRecord × TTWState) TTWState )
          let walkstate : TTWState :=
            { walkstate with permissions := { walkstate.permissions with ap := ap } }
          let walkstate : TTWState :=
            { walkstate with permissions := { walkstate.permissions with xn := xn } }
          let walkstate : TTWState :=
            { walkstate with permissions := { walkstate.permissions with pxn := pxn } }
          let walkstate : TTWState := { walkstate with domain := domain }
          let walkstate : TTWState := { walkstate with nG := nG }
          let walkstate : TTWState :=
            if (((BEq.beq accdesc.ss SS_Secure) && (ns == 0#1)) : Bool)
            then
              { walkstate with baseaddress := { walkstate.baseaddress with paspace := PAS_Secure } }
            else
              { walkstate with baseaddress := { walkstate.baseaddress with paspace := PAS_NonSecure } }
          let w__40 ← (( do readReg __tlb_enabled ) : SailME (FaultRecord × TTWState) Bool )
          if (w__40 : Bool)
          then
            (do
              let tlbcontext : TLBContext := { tlbcontext with xs := walkstate.memattrs.xs }
              let tlbcontext : TLBContext := { tlbcontext with nG := walkstate.nG }
              let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 2630) ()) ) : SailME
                (FaultRecord × TTWState) TLBRecord )
              let tlbrecord : TLBRecord := { tlbrecord with context := tlbcontext }
              let tlbrecord : TLBRecord := { tlbrecord with walkstate := walkstate }
              let tlbrecord : TLBRecord :=
                { tlbrecord with blocksize := (AArch32_TranslationSizeSD walkstate.sdftype) }
              let tlbrecord : TLBRecord := { tlbrecord with contigsize := 0 }
              (pure ((S1TLBCache tlbrecord))))
          else (pure (()))
          (pure ((fault, walkstate)))))


end ArmFull.Functions
