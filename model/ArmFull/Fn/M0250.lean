import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0047
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0062
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0113
import ArmFull.Fn.M0117
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0152
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0194
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0204
import ArmFull.Fn.M0212
import ArmFull.Fn.M0215
import ArmFull.Fn.M0226
import ArmFull.Fn.M0227
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0238
import ArmFull.Fn.M0239
import ArmFull.Fn.M0241
import ArmFull.Fn.M0244
import ArmFull.Fn.M0247
import ArmFull.Fn.M0248

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

def AArch64_PMUCycle (_ : Unit) : SailM Unit := do
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
  then
    (do
      let w__3 ← (( do (ShouldBRBEFreeze ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (BRBEFreeze ()))
      else (pure (())))
  else
    (do
      let w__4 ← (( do (HavePMUv3 ()) ) : SailM Bool )
      if ((! w__4) : Bool)
      then (pure (()))
      else
        (do
          (PMUEvent PMU_EVENT_CPU_CYCLES)
          let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
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
                    ArmFull.assert ((0 ≤b idx) && (idx ≤b 32)) "sail-arm/v8_base.sail:34466.65-34466.66"
                    let w__5 ← (( do (CountPMUEvents (Sail.Int.toNatChecked (idx))) ) : SailM Bool
                      )
                    if (w__5 : Bool)
                    then
                      (do
                        ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:34468.68-34468.69"
                        let w__6 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
                        let accumulated : Int :=
                          (GetElem?.getElem! w__6 (Sail.Int.toNatChecked (idx)))
                        (AArch64_IncrementEventCounter (Sail.Int.toNatChecked (idx)) accumulated))
                    else (pure (()))
                    ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:34472.64-34472.65"
                    let w__7 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
                    writeReg PMUEventAccumulator (vectorUpdate w__7 (Sail.Int.toNatChecked (idx)) 0)
                (pure loop_vars)))
          else (pure (()))
          (AArch64_IncrementCycleCounter ())
          (CheckForPMUOverflow ())))


def AArch64_ExceptionReturn (new_pc_in : (BitVec 64)) (spsr : (BitVec 64)) : SailM Unit := do
  let iesb_req ← (( do (undefined_bool_at (← occLabel 2454) ()) ) : SailM Bool )
  let sync_errors ← (( do (undefined_bool_at (← occLabel 2455) ()) ) : SailM Bool )
  let new_pc : (BitVec 64) := new_pc_in
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))
  let w__3 ← (( do (HaveIESB ()) ) : SailM Bool )
  let sync_errors ← (( do
    if (w__3 : Bool)
    then
      (do
        let w__4 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        let sync_errors : Bool := (((_get_SCTLRType_IESB w__4) == 1#1) : Bool)
        let w__5 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
        let sync_errors ← (( do
          if (w__5 : Bool)
          then
            (do
              if ((sync_errors : Bool) : Bool)
              then (pure true)
              else
                (do
                  if ((← do
                       let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                       let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                       (pure (((((_get_SCR_EL3_Type_EA w__6) +++ (_get_SCR_EL3_Type_NMEA w__7)) == 0b11#2) : Bool)))) : Bool)
                  then
                    (do
                      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__8.EL == EL3) : Bool))))
                  else (pure false)))
          else (pure (sync_errors)) ) : SailM Bool )
        if (sync_errors : Bool)
        then
          (do
            let _ : Unit := (SynchronizeErrors ())
            let iesb_req : Bool := true
            (TakeUnmaskedPhysicalSErrorInterrupts iesb_req))
        else (pure (()))
        (pure (sync_errors)))
    else (pure (sync_errors)) ) : SailM Bool )
  let sync_errors := sync_errors
  let _ : Unit := (SynchronizeContext ())
  writeReg __InstructionStep false
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  let source_el : (BitVec 2) := w__11.EL
  let illegal_psr_state ← (( do (IllegalExceptionReturn spsr) ) : SailM Bool )
  (SetPSTATEFromPSR__1 spsr illegal_psr_state)
  let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
  (SendEventLocal ())
  let new_pc ← (( do
    if ((illegal_psr_state && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 4)])) == 1#1)) : Bool)
    then
      (do
        let w__12 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
        let new_pc := ((Sail.BitVec.updateSubrange new_pc 63 32 w__12) : (BitVec 64))
        let w__13 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
        let new_pc := ((Sail.BitVec.updateSubrange new_pc 1 0 w__13) : (BitVec 64))
        (pure (new_pc)))
    else
      (do
        let w__14 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        if (w__14 : Bool)
        then
          (do
            let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
            let new_pc : (BitVec 64) :=
              if ((w__15.T == 1#1) : Bool)
              then (BitVec.update new_pc 0 (Bit 0#1))
              else (Sail.BitVec.updateSubrange new_pc 1 0 0b00#2)
            (pure (new_pc)))
        else
          (do
            let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
            (AArch64_BranchAddr new_pc w__16.EL))) ) : SailM (BitVec 64) )
  let w__18 ← (( do (HaveBRBExt ()) ) : SailM Bool )
  if (w__18 : Bool)
  then
    (do
      (BRBEExceptionReturn new_pc source_el))
  else (pure (()))
  let w__19 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__19 : Bool)
  then
    (do
      let w__22 ← (( do
        if ((← do
             (HaveSME ())) : Bool)
        then
          (do
            let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__21.SM == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__22 : Bool)
      then
        (do
          (ResetSVEState ()))
      else (pure (()))
      let branch_conditional : Bool := false
      (BranchTo (Sail.BitVec.extractLsb new_pc 31 0) BranchType_ERET branch_conditional))
  else
    (do
      (BranchToAddr new_pc BranchType_ERET))
  (CheckExceptionCatch false)


def AArch32_S2Walk (fault_in : FaultRecord) (walkparams : S2TTWParams) (s1level : (Option Int)) (accdesc : AccessDescriptor) (ipa : AddressDescriptor) : SailM (FaultRecord × TTWState) := SailME.run do
  let finalwalkstate ← (( do (undefined_TTWState (← occLabel 2542) ()) ) : SailME
    (FaultRecord × TTWState) TTWState )
  let fault : FaultRecord := fault_in
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2543) ()) ) : SailME
    (FaultRecord × TTWState) TLBContext )
  let w__0 ← (( do readReg __tlb_enabled ) : SailME (FaultRecord × TTWState) Bool )
  let (fault, tlbcontext) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (AArch32_GetS2TLBContext ipa.paddress) ) : SailME
          (FaultRecord × TTWState) TLBContext )
        let tlbcontext := (w__1 : TLBContext)
        let tlbentry ← (( do (S2TLBLookup tlbcontext) ) : SailME (FaultRecord × TTWState) TLBLine
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
  if (((let b__0 := walkparams.sl0
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) || (AArch32_S2InconsistentSL walkparams)) : Bool)
  then
    (do
      let fault : FaultRecord := { fault with statuscode := Fault_Translation }
      let fault : FaultRecord := { fault with level := 1 }
      let w__2 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState) TTWState )
      (pure ((fault, w__2))))
  else
    (do
      let iasize : Int := (AArch32_S2IASize walkparams.t0sz)
      let startlevel : Int := (AArch32_S2StartLevel walkparams.sl0)
      let levels : Int := (FINAL_LEVEL -i startlevel)
      let granulebits : Int := (TGxGranuleBits walkparams.tgx)
      let stride : Int := (granulebits -i 3)
      let w__3 ← (( do readReg VTTBR ) : SailME (FaultRecord × TTWState) (BitVec 64) )
      if ((! (IsZero (Sail.BitVec.extractLsb w__3 47 40))) : Bool)
      then
        (do
          let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
          let fault : FaultRecord := { fault with level := 0 }
          let w__4 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState) TTWState )
          (pure ((fault, w__4))))
      else
        (do
          let baseaddress ← (( do (undefined_FullAddress (← occLabel 2544) ()) ) : SailME
            (FaultRecord × TTWState) FullAddress )
          let baselsb : Int := ((iasize -i ((levels *i stride) +i granulebits)) +i 3)
          let baseaddress : FullAddress := { baseaddress with paspace := PAS_NonSecure }
          ArmFull.assert ((0 ≤b baselsb) && (baselsb ≤b 39)) "sail-arm/v8_base.sail:37878.55-37878.56"
          let w__5 ← (( do readReg VTTBR ) : SailME (FaultRecord × TTWState) (BitVec 64) )
          let baseaddress :=
            ({ baseaddress with address := (Sail.BitVec.zeroExtend
                ((Sail.BitVec.extractLsb w__5 39 (Sail.Int.toNatChecked (baselsb))) +++ (Zeros
                    (n := (Sail.Int.toNatChecked (baselsb))))) 56) } : FullAddress)
          let walkstate ← (( do (undefined_TTWState (← occLabel 2545) ()) ) : SailME
            (FaultRecord × TTWState) TTWState )
          let walkstate : TTWState := { walkstate with baseaddress := baseaddress }
          let walkstate : TTWState := { walkstate with level := startlevel }
          let walkstate : TTWState := { walkstate with istable := true }
          let w__6 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) : SailME
            (FaultRecord × TTWState) MemoryAttributes )
          let walkstate := ({ walkstate with memattrs := w__6 } : TTWState)
          let indexmsb : Int := (iasize -i 1)
          let descriptor ← (( do (undefined_bitvector_at (← occLabel 2546) 64) ) : SailME
            (FaultRecord × TTWState) (BitVec 64) )
          let walkaccess ← (( do (CreateAccDescS2TTW accdesc) ) : SailME (FaultRecord × TTWState)
            AccessDescriptor )
          let walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 2547) ()) ) : SailME
            (FaultRecord × TTWState) AddressDescriptor )
          let walkaddress : AddressDescriptor := { walkaddress with vaddress := ipa.vaddress }
          let w__7 ← (( do (HCR2_read ()) ) : SailME (FaultRecord × TTWState) (BitVec 32) )
          let walkaddress ← (( do
            if (((_get_HCR2_Type_CD w__7) == 1#1) : Bool)
            then
              (do
                let w__8 ← (( do (NormalNCMemAttr ()) ) : SailME (FaultRecord × TTWState)
                  MemoryAttributes )
                let walkaddress := ({ walkaddress with memattrs := w__8 } : AddressDescriptor)
                let walkaddress : AddressDescriptor :=
                  { walkaddress with memattrs := { walkaddress.memattrs with xs := walkstate.memattrs.xs } }
                (pure (walkaddress)))
            else
              (let walkaddress : AddressDescriptor :=
                { walkaddress with memattrs := walkstate.memattrs }
              (pure (walkaddress))) ) : SailME (FaultRecord × TTWState) AddressDescriptor )
          let walkaddress : AddressDescriptor :=
            { walkaddress with memattrs := { walkaddress.memattrs with shareability := (EffectiveShareability
                  walkaddress.memattrs) } }
          let indexlsb ← (( do (undefined_int_at (← occLabel 2548) ()) ) : SailME
            (FaultRecord × TTWState) Int )
          let desctype ← (( do (undefined_DescriptorType (← occLabel 2549) ()) ) : SailME
            (FaultRecord × TTWState) DescriptorType )
          let (descriptor, desctype, fault, indexlsb, indexmsb, walkaddress, walkstate) ← (( do
            let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (descriptor, desctype, fault, indexlsb, indexmsb, walkaddress, walkstate) => (pure (BEq.beq
                desctype DescriptorType_Leaf))) (descriptor, desctype, fault, indexlsb, indexmsb, walkaddress, walkstate)
              fun (descriptor, desctype, fault, indexlsb, indexmsb, walkaddress, walkstate) => do
                let fault : FaultRecord := { fault with level := walkstate.level }
                let indexlsb : Int := (((FINAL_LEVEL -i walkstate.level) *i stride) +i granulebits)
                let indexmsb : Int := indexmsb
                let indexlsb : Int := indexlsb
                ArmFull.assert ((0 ≤b indexlsb) && ((indexlsb ≤b indexmsb) && (indexmsb <b 56))) "sail-arm/v8_base.sail:37905.91-37905.92"
                ArmFull.assert (40 ≥b (((indexmsb -i indexlsb) +i 1) +i 3)) "sail-arm/v8_base.sail:37906.68-37906.69"
                let index : (BitVec 40) :=
                  (Sail.BitVec.zeroExtend
                    ((Sail.BitVec.extractLsb ipa.paddress.address (Sail.Int.toNatChecked (indexmsb))
                        (Sail.Int.toNatChecked (indexlsb))) +++ 0b000#3) 40)
                let walkaddress : AddressDescriptor :=
                  { walkaddress with paddress := { walkaddress.paddress with address := (walkstate.baseaddress.address ||| (Sail.BitVec.castWidth (m := 56) (Sail.BitVec.zeroExtend
                          index 56))) } }
                let walkaddress : AddressDescriptor :=
                  { walkaddress with paddress := { walkaddress.paddress with paspace := walkstate.baseaddress.paspace } }
                let translation_info : TranslationInfo :=
                  { regime := Regime_EL10
                    vmid := none
                    asid := none
                    va := walkaddress.vaddress
                    s1level := s1level
                    s2info := (some
                        ((Sail.BitVec.zeroExtend ipa.paddress.address 64), walkstate.level))
                    s1params := none
                    s2params := (some walkparams)
                    memattrs := walkaddress.memattrs }
                let w__9 ← (( do
                  (FetchDescriptor walkparams.ee walkaddress walkaccess fault 64 translation_info) )
                  : SailME (FaultRecord × TTWState) (FaultRecord × (BitVec 64)) )
                let (tup__0, tup__1) := (w__9 : (FaultRecord × (BitVec 64)))
                let fault : FaultRecord := tup__0
                let descriptor : (BitVec 64) := tup__1
                let (desctype, fault, indexmsb, walkstate) ← (( do
                  if ((bne fault.statuscode Fault_None) : Bool)
                  then
                    (do
                      let w__10 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                        (FaultRecord × TTWState) TTWState )
                      SailME.throw ((fault, w__10) : (FaultRecord × TTWState))
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
                                let w__11 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                  (FaultRecord × TTWState) TTWState )
                                SailME.throw ((fault, w__11) : (FaultRecord × TTWState))
                                (pure ((fault, indexmsb, walkstate))))
                            else
                              (let walkstate : TTWState :=
                                { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                                      ((Sail.BitVec.extractLsb descriptor 39 12) +++ (Zeros
                                          (n := 12))) 56) } }
                              let walkstate : TTWState :=
                                { walkstate with level := (walkstate.level +i 1) }
                              let indexmsb : Int := (indexlsb -i 1)
                              (pure ((fault, indexmsb, walkstate)))))
                        | .DescriptorType_Invalid =>
                          (do
                            let fault : FaultRecord :=
                              { fault with statuscode := Fault_Translation }
                            let w__12 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                              (FaultRecord × TTWState) TTWState )
                            SailME.throw ((fault, w__12) : (FaultRecord × TTWState))
                            (pure ((fault, indexmsb, walkstate))))
                        | .DescriptorType_Leaf =>
                          (let walkstate : TTWState := { walkstate with istable := false }
                          (pure ((fault, indexmsb, walkstate)))) ) : SailME
                        (FaultRecord × TTWState) (FaultRecord × Int × TTWState) )
                      (pure ((desctype, fault, indexmsb, walkstate)))) ) : SailME
                  (FaultRecord × TTWState) (DescriptorType × FaultRecord × Int × TTWState) )
                (pure ((descriptor, desctype, fault, indexlsb, indexmsb, walkaddress, walkstate)))
            (pure loop_vars) ) : SailME (FaultRecord × TTWState)
            ((BitVec 64) × DescriptorType × FaultRecord × Int × Int × AddressDescriptor × TTWState)
            )
          let indexlsb : Int := indexlsb
          if ((! (IsZero (Sail.BitVec.extractLsb descriptor 47 40))) : Bool)
          then
            (do
              let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
              let w__13 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState)
                TTWState )
              (pure ((fault, w__13))))
          else
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)])) == 0#1) : Bool)
              then
                (do
                  let fault : FaultRecord := { fault with statuscode := Fault_AccessFlag }
                  let w__14 ← (( do (__UNKNOWN_TTWState ()) ) : SailME (FaultRecord × TTWState)
                    TTWState )
                  (pure ((fault, w__14))))
              else
                (do
                  ArmFull.assert ((0 ≤b indexlsb) && (indexlsb ≤b 39)) "sail-arm/v8_base.sail:37955.57-37955.58"
                  let walkstate : TTWState :=
                    { walkstate with baseaddress := { walkstate.baseaddress with address := (Sail.BitVec.zeroExtend
                          ((Sail.BitVec.extractLsb descriptor 39 (Sail.Int.toNatChecked (indexlsb))) +++ (Zeros
                              (n := (Sail.Int.toNatChecked (indexlsb))))) 56) } }
                  let walkstate : TTWState :=
                    { walkstate with permissions := { walkstate.permissions with s2ap := (Sail.BitVec.extractLsb
                          descriptor 7 6) } }
                  let walkstate : TTWState :=
                    { walkstate with permissions := { walkstate.permissions with s2xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                            descriptor 54)])) } }
                  let w__15 ← (( do (HaveExtendedExecuteNeverExt ()) ) : SailME
                    (FaultRecord × TTWState) Bool )
                  let walkstate : TTWState :=
                    if (w__15 : Bool)
                    then
                      { walkstate with permissions := { walkstate.permissions with s2xnx := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              descriptor 53)])) } }
                    else
                      { walkstate with permissions := { walkstate.permissions with s2xnx := 0#1 } }
                  let memattr : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 5 2)
                  let sh : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 9 8)
                  let s2aarch64 : Bool := false
                  let w__16 ← (( do (S2DecodeMemAttrs memattr sh s2aarch64) ) : SailME
                    (FaultRecord × TTWState) MemoryAttributes )
                  let walkstate := ({ walkstate with memattrs := w__16 } : TTWState)
                  let walkstate : TTWState :=
                    { walkstate with contiguous := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 52)])) }
                  let w__17 ← (( do readReg __tlb_enabled ) : SailME (FaultRecord × TTWState)
                    Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      let tlbcontext : TLBContext := { tlbcontext with xs := walkstate.memattrs.xs }
                      let tlbcontext : TLBContext := { tlbcontext with level := walkstate.level }
                      let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 2550) ()) ) :
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
                            let w__18 ← (( do
                              (ContiguousSize walkparams.d128 walkparams.tgx walkstate.level) ) :
                              SailME (FaultRecord × TTWState) Int )
                            let tlbrecord := ({ tlbrecord with contigsize := w__18 } : TLBRecord)
                            (pure (tlbrecord)))
                        else
                          (let tlbrecord : TLBRecord := { tlbrecord with contigsize := 0 }
                          (pure (tlbrecord))) ) : SailME (FaultRecord × TTWState) TLBRecord )
                      (pure ((S2TLBCache tlbrecord))))
                  else (pure (()))
                  (pure ((fault, walkstate)))))))


/-- Type quantifiers: size : Int -/
def AArch32_CheckDebug (vaddress : (BitVec 32)) (accdesc : AccessDescriptor) (size : Int) : SailM FaultRecord := do
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let d_side : Bool := ((IsDataAccess accdesc.acctype) || (BEq.beq accdesc.acctype AccessType_DC))
  let i_side : Bool := (BEq.beq accdesc.acctype AccessType_IFETCH)
  let generate_exception ← (( do
    if ((← do
         (AArch32_GenerateDebugExceptions ())) : Bool)
    then
      (do
        let w__1 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_DBGDSCRext_Type_MDBGen w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let halt ← (( do (HaltOnBreakpointOrWatchpoint ()) ) : SailM Bool )
  let vector_catch_first_name ← (( do (ConstrainUnpredictableBool Unpredictable_BPVECTORCATCHPRI)
    ) : SailM Bool )
  let fault ← (( do
    if (((i_side && vector_catch_first_name) && generate_exception) : Bool)
    then
      (do
        (AArch32_CheckVectorCatch fault vaddress size))
    else (pure (fault)) ) : SailM FaultRecord )
  let fault ← (( do
    if (((BEq.beq fault.statuscode Fault_None) && (generate_exception || halt)) : Bool)
    then
      (do
        if (d_side : Bool)
        then
          (do
            (AArch32_CheckWatchpoint fault vaddress accdesc size))
        else
          (do
            if (i_side : Bool)
            then
              (do
                (AArch32_CheckBreakpoint fault vaddress accdesc size))
            else (pure (fault))))
    else (pure (fault)) ) : SailM FaultRecord )
  if (((((BEq.beq fault.statuscode Fault_None) && i_side) && (! vector_catch_first_name)) && generate_exception) : Bool)
  then
    (do
      (AArch32_CheckVectorCatch fault vaddress size))
  else (pure (fault))


def AArch32_ExceptionReturn (new_pc_in : (BitVec 32)) (spsr : (BitVec 32)) : SailM Unit := do
  let new_pc : (BitVec 32) := new_pc_in
  let _ : Unit := (SynchronizeContext ())
  writeReg __InstructionStep false
  (SetPSTATEFromPSR spsr)
  let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
  (SendEventLocal ())
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let new_pc ← (( do
    if ((w__0.IL == 1#1) : Bool)
    then
      (do
        let w__1 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
        let new_pc := ((Sail.BitVec.updateSubrange new_pc 1 0 w__1) : (BitVec 32))
        (pure (new_pc)))
    else
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        let new_pc : (BitVec 32) :=
          if ((w__2.T == 1#1) : Bool)
          then (BitVec.update new_pc 0 (Bit 0#1))
          else (Sail.BitVec.updateSubrange new_pc 1 0 0b00#2)
        (pure (new_pc))) ) : SailM (BitVec 32) )
  let b__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
  let branch_conditional : Bool :=
    (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b111#3 : (BitVec 3))) : Bool)
      then true
      else false : Bool))
  (BranchTo new_pc BranchType_ERET branch_conditional)
  (CheckExceptionCatch false)


def AArch64_BranchTargetException (vaddress : (BitVec 52)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_BranchTarget) ) : SailM ExceptionRecord )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 w__0.BTYPE) } : ExceptionRecord)
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 2 (Zeros (n := 23))) }
  let target_el : (BitVec 2) := EL1
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let target_el ← (( do
    if (((BitVec.toNat w__1.EL) >b (BitVec.toNat EL1)) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        let target_el := (w__2.EL : (BitVec 2))
        (pure (target_el)))
    else
      (do
        let w__7 ← (( do
          if ((← do
               if ((← do
                    let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__3.EL == EL0) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__7 : Bool)
          then EL2
          else target_el
        (pure (target_el))) ) : SailM (BitVec 2) )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_WFxTrap (wfxtype : WFxType) (target_el : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert ((BitVec.toNat target_el) >b (BitVec.toNat w__0.EL)) "sail-arm/v8_base.sail:10642.44-10642.45"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_WFxTrap) ) : SailM ExceptionRecord )
  let w__1 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20 w__1) } : ExceptionRecord)
  let except ← (( do
    match wfxtype with
    | .WFxType_WFI =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b00#2) }
      (pure (except)))
    | .WFxType_WFE =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b01#2) }
      (pure (except)))
    | .WFxType_WFIT =>
      (do
        let except : ExceptionRecord :=
          { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b10#2) }
        let except : ExceptionRecord :=
          { except with syndrome := (BitVec.update except.syndrome 2 (Bit 1#1)) }
        let w__2 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
        let except :=
          ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
              (Sail.BitVec.extractLsb w__2 4 0)) } : ExceptionRecord)
        (pure (except)))
    | .WFxType_WFET =>
      (do
        let except : ExceptionRecord :=
          { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b11#2) }
        let except : ExceptionRecord :=
          { except with syndrome := (BitVec.update except.syndrome 2 (Bit 1#1)) }
        let w__3 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
        let except :=
          ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
              (Sail.BitVec.extractLsb w__3 4 0)) } : ExceptionRecord)
        (pure (except))) ) : SailM ExceptionRecord )
  let w__7 ← (( do
    if ((← do
         if (((target_el == EL1) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else
    (do
      (AArch64_TakeException target_el except preferred_exception_return vect_offset))


end ArmFull.Functions
