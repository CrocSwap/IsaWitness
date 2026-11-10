import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0038
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0155
import ArmFull.Fn.M0156
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0185
import ArmFull.Fn.M0188
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0204

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

def BTypeCompatible_PACIXSP (_ : Unit) : SailM Bool := do
  let index ← (( do (undefined_int_at (← occLabel 1346) ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.BTYPE == 0b01#2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.BTYPE == 0b10#2) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (true))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__3.BTYPE == 0b11#2) : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          let index : Int :=
            if ((w__4.EL == EL0) : Bool)
            then 35
            else 36
          let w__5 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
          (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__5
                  (Sail.Int.toNatChecked (index)))])) == 0#1))))
      else (pure (false)))


/-- Type quantifiers: size : Int -/
def AArch64_UnalignedAccessFaults (accdesc : AccessDescriptor) (address : (BitVec 64)) (size : Int) : SailM Bool := do
  let w__0 ← (( do (AlignmentEnforced ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (true))
  else
    (do
      if ((BEq.beq accdesc.acctype AccessType_GCS) : Bool)
      then (pure (true))
      else
        (do
          if (accdesc.rcw : Bool)
          then (pure (true))
          else
            (do
              if (accdesc.ls64 : Bool)
              then (pure (true))
              else
                (do
                  if ((accdesc.exclusive || accdesc.atomicop) : Bool)
                  then
                    (do
                      if ((← do
                           let w__1 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
                           (pure (((! w__1) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__2 ← (( do (AllInAlignedQuantity address size 16) ) : SailM Bool )
                          (pure (((! w__2) : Bool)))))
                  else
                    (do
                      if (((accdesc.acqsc || accdesc.acqpc) || accdesc.relsc) : Bool)
                      then
                        (do
                          if ((← do
                               let w__4 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
                               (pure (((! w__4) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              if ((← do
                                   let w__5 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
                                   (pure ((((_get_SCTLRType_nAA w__5) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  let w__6 ← (( do (AllInAlignedQuantity address size 16) ) :
                                    SailM Bool )
                                  (pure (((! w__6) : Bool))))
                              else (pure false)))
                      else (pure (false)))))))


def AArch64_AccessIsTagChecked (vaddr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM Bool := do
  ArmFull.assert accdesc.tagchecked "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22846.29-22846.30"
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let is_instr : Bool := false
      let w__5 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             let w__2 ← (( do (EffectiveMTX vaddr is_instr w__1.EL) ) : SailM (BitVec 1) )
             (pure (((w__2 == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
            let w__4 ← (( do (EffectiveTBI vaddr is_instr w__3.EL) ) : SailM (BitVec 1) )
            (pure (((w__4 == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then (pure (false))
      else
        (do
          let w__8 ← (( do
            (pure ((← do
                  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__7 ← (( do (EffectiveTCMA vaddr w__6.EL) ) : SailM (BitVec 1) )
                  (pure (((w__7 == 1#1) : Bool)))) && ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                      vaddr 59 55)) == 0b00000#5) || ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                      vaddr 59 55)) == 0b11111#5)) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then (pure (false))
          else
            (do
              let w__9 ← (( do (AArch64_AllocationTagAccessIsEnabled accdesc.el) ) : SailM Bool )
              if ((! w__9) : Bool)
              then (pure (false))
              else
                (do
                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__10.TCO == 1#1) : Bool)
                  then (pure (false))
                  else
                    (do
                      let w__14 ← (( do
                        if ((← do
                             (pure ((← do
                                   (HaveMTEStoreOnlyExt ())) && ((! accdesc.write) : Bool)))) : Bool)
                        then
                          (do
                            (StoreOnlyTagCheckingEnabled accdesc.el))
                        else (pure false) ) : SailM Bool )
                      let w__15 : Bool :=
                        if (w__14 : Bool)
                        then false
                        else true
                      (pure (w__15)))))))


/-- Type quantifiers: k_ex10456189_ : Bool -/
def C27bReservedBP32 (bt_in : (BitVec 4)) (context_aware : Bool) : SailM Bool := do
  let bt : (BitVec 4) := bt_in
  let reserved : Bool := false
  let w__1 ← (( do
    if ((let b__0 := bt
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) : Bool)
    then
      (do
        (HaltOnBreakpointOrWatchpoint ()))
    else (pure false) ) : SailM Bool )
  let reserved : Bool :=
    if (w__1 : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if (((let b__1 := bt
         (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                    b__1 1 1)) == (0#1 : (BitVec 1)))) : Bool)
           then true
           else false : Bool))) && (! context_aware)) : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if (((let b__2 := bt
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 3 3)) == (1#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool)) && (! (HaveEL EL2))) : Bool)
    then true
    else reserved
  let w__5 ← (( do
    if ((← do
         if ((let b__3 := bt
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
            then true
            else
              (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
              then true
              else false) : Bool)) : Bool)
         then
           (do
             let w__2 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
             (pure (((! w__2) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (HaveV82Debug ()) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let reserved : Bool :=
    if (w__5 : Bool)
    then true
    else reserved
  (pure (reserved))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 64 -/
def IsBreakpointEnabled (n : Nat) : SailM Bool := do
  let w__7 ← (( do
    if (((n >b 15) : Bool) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__0 ← (( do (HaltOnBreakpointOrWatchpoint ()) ) : SailM Bool )
                  (pure (((! w__0) : Bool)))) : Bool)
             then
               (do
                 let w__1 ← (( do (SelfHostedExtendedBPWPEnabled ()) ) : SailM Bool )
                 (pure (((! w__1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (HaltOnBreakpointOrWatchpoint ())) : Bool)
            then
              (do
                let w__4 ← (( do (EDSCR2_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_EDSCR2_Type_EHBWE w__4) == 0#1) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  if (w__7 : Bool)
  then (pure (false))
  else
    (do
      let w__8 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      (pure (((_get_DBGBCR_EL1_Type_E (GetElem?.getElem! w__8 n)) == 1#1))))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 64 -/
def IsWatchpointEnabled (n : Nat) : SailM Bool := do
  let w__7 ← (( do
    if (((n >b 15) : Bool) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__0 ← (( do (HaltOnBreakpointOrWatchpoint ()) ) : SailM Bool )
                  (pure (((! w__0) : Bool)))) : Bool)
             then
               (do
                 let w__1 ← (( do (SelfHostedExtendedBPWPEnabled ()) ) : SailM Bool )
                 (pure (((! w__1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (HaltOnBreakpointOrWatchpoint ())) : Bool)
            then
              (do
                let w__4 ← (( do (EDSCR2_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_EDSCR2_Type_EHBWE w__4) == 0#1) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  if (w__7 : Bool)
  then (pure (false))
  else
    (do
      let w__8 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      (pure (((_get_DBGWCR_EL1_Type_E (GetElem?.getElem! w__8 n)) == 1#1))))


def AArch64_S1CheckPermissions (fault_in : FaultRecord) (regime : Regime) (walkstate : TTWState) (walkparams : S1TTWParams) (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault : FaultRecord := fault_in
  let permissions : Permissions := walkstate.permissions
  let s1perms ← (( do (AArch64_S1ComputePermissions regime walkstate walkparams accdesc) ) : SailM
    S1AccessControls )
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then
    (do
      if ((s1perms.overlay && (s1perms.ox == 0#1)) : Bool)
      then
        (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
        let fault : FaultRecord := { fault with overlay := true }
        (pure (fault)))
      else
        (do
          let w__1 ← (( do
            if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
            then
              (do
                let w__0 ← (( do (ConstrainUnpredictable Unpredictable_INSTRDEVICE) ) : SailM
                  Constraint )
                (pure (((BEq.beq w__0 Constraint_FAULT) : Bool))))
            else (pure false) ) : SailM Bool )
          let fault : FaultRecord :=
            if (w__1 : Bool)
            then { fault with statuscode := Fault_Permission }
            else
              (if ((s1perms.x == 0#1) : Bool)
              then { fault with statuscode := Fault_Permission }
              else fault)
          (pure (fault))))
  else
    (do
      if ((BEq.beq accdesc.acctype AccessType_DC) : Bool)
      then
        (let fault : FaultRecord :=
          if ((BEq.beq accdesc.cacheop CacheOp_Invalidate) : Bool)
          then
            (if ((s1perms.overlay && (s1perms.ow == 0#1)) : Bool)
            then
              (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
              { fault with overlay := true })
            else
              (if ((s1perms.w == 0#1) : Bool)
              then { fault with statuscode := Fault_Permission }
              else fault))
          else
            (if ((accdesc.el == EL0) : Bool)
            then
              (if ((s1perms.overlay && (s1perms.or == 0#1)) : Bool)
              then
                (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                { fault with overlay := true })
              else
                (if ((((((walkparams.cmow == 1#1) && (BEq.beq accdesc.opscope CacheOpScope_PoC)) && (BEq.beq
                           accdesc.cacheop CacheOp_CleanInvalidate)) && s1perms.overlay) && (s1perms.ow == 0#1)) : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                  { fault with overlay := true })
                else
                  (if ((s1perms.r == 0#1) : Bool)
                  then { fault with statuscode := Fault_Permission }
                  else
                    (if (((((walkparams.cmow == 1#1) && (BEq.beq accdesc.opscope CacheOpScope_PoC)) && (BEq.beq
                             accdesc.cacheop CacheOp_CleanInvalidate)) && (s1perms.w == 0#1)) : Bool)
                    then { fault with statuscode := Fault_Permission }
                    else fault))))
            else fault)
        (pure (fault)))
      else
        (do
          if ((BEq.beq accdesc.acctype AccessType_IC) : Bool)
          then
            (do
              if ((accdesc.el == EL0) : Bool)
              then
                (do
                  let w__3 ← (( do
                    if (((s1perms.overlay && (s1perms.or == 0#1)) : Bool) : Bool)
                    then
                      (do
                        (__IMPDEF_boolean "Permission fault on EL0 IC_IVAU execution"))
                    else (pure false) ) : SailM Bool )
                  if (w__3 : Bool)
                  then
                    (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                    let fault : FaultRecord := { fault with overlay := true }
                    (pure (fault)))
                  else
                    (do
                      if ((((walkparams.cmow == 1#1) && s1perms.overlay) && (s1perms.ow == 0#1)) : Bool)
                      then
                        (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                        let fault : FaultRecord := { fault with overlay := true }
                        (pure (fault)))
                      else
                        (do
                          let w__5 ← (( do
                            if (((s1perms.r == 0#1) : Bool) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "Permission fault on EL0 IC_IVAU execution"))
                            else (pure false) ) : SailM Bool )
                          let fault : FaultRecord :=
                            if (w__5 : Bool)
                            then { fault with statuscode := Fault_Permission }
                            else
                              (if (((walkparams.cmow == 1#1) && (s1perms.w == 0#1)) : Bool)
                              then { fault with statuscode := Fault_Permission }
                              else fault)
                          (pure (fault)))))
              else (pure (fault)))
          else
            (do
              let w__7 ← (( do
                (pure ((← do
                      (HaveGCS ())) && ((BEq.beq accdesc.acctype AccessType_GCS) : Bool))) ) : SailM
                Bool )
              let fault : FaultRecord :=
                if (w__7 : Bool)
                then
                  (if ((s1perms.gcs == 0#1) : Bool)
                  then { fault with statuscode := Fault_Permission }
                  else
                    (if (((accdesc.write && ((walkparams.ha +++ walkparams.hd) != 0b11#2)) && (permissions.ndirty == 1#1)) : Bool)
                    then
                      (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                      let fault : FaultRecord := { fault with dirtybit := true }
                      { fault with write := true })
                    else fault))
                else
                  (if (((accdesc.read && s1perms.overlay) && (s1perms.or == 0#1)) : Bool)
                  then
                    (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                    let fault : FaultRecord := { fault with overlay := true }
                    { fault with write := false })
                  else
                    (if (((accdesc.write && s1perms.overlay) && (s1perms.ow == 0#1)) : Bool)
                    then
                      (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                      let fault : FaultRecord := { fault with overlay := true }
                      { fault with write := true })
                    else
                      (if ((accdesc.read && (s1perms.r == 0#1)) : Bool)
                      then
                        (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                        { fault with write := false })
                      else
                        (if ((accdesc.write && (s1perms.w == 0#1)) : Bool)
                        then
                          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                          { fault with write := true })
                        else
                          (if (((accdesc.write && accdesc.tagaccess) && (BEq.beq
                                 walkstate.memattrs.tags MemTag_CanonicallyTagged)) : Bool)
                          then
                            (let fault : FaultRecord :=
                              { fault with statuscode := Fault_Permission }
                            let fault : FaultRecord := { fault with write := true }
                            { fault with s1tagnotdata := true })
                          else
                            (if ((((accdesc.write && (! ((walkparams.ha +++ walkparams.hd) == 0b11#2))) && (walkparams.pie == 1#1)) && (permissions.ndirty == 1#1)) : Bool)
                            then
                              (let fault : FaultRecord :=
                                { fault with statuscode := Fault_Permission }
                              let fault : FaultRecord := { fault with dirtybit := true }
                              { fault with write := true })
                            else fault))))))
              (pure (fault)))))


def AArch64_TLBContextEL10 (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1472) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL10 }
  let w__0 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
  let tlbcontext := ({ tlbcontext with vmid := w__0 } : TLBContext)
  let w__1 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  let w__4 ← (( do
    if (((_get_TCR_EL1_Type_A1 w__1) == 0#1) : Bool)
    then
      (do
        let w__2 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
        (pure ((_get_TTBR0_EL1_Type_ASID w__2))))
    else
      (do
        let w__3 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
        (pure ((_get_TTBR1_EL1_Type_ASID w__3)))) ) : SailM (BitVec 16) )
  let tlbcontext := ({ tlbcontext with asid := w__4 } : TLBContext)
  let w__5 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  let tlbcontext : TLBContext :=
    if (((_get_TCR_EL1_Type_AS w__5) == 0#1) : Bool)
    then
      { tlbcontext with asid := (Sail.BitVec.updateSubrange tlbcontext.asid 15 8 (Zeros (n := 8))) }
    else tlbcontext
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := va }
  let w__6 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      if ((BEq.beq (AArch64_GetVARange va) VARange_LOWER) : Bool)
      then
        (do
          let w__7 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR0_EL1_Type_CnP w__7) } : TLBContext)
          (pure (tlbcontext)))
      else
        (do
          let w__8 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR1_EL1_Type_CnP w__8) } : TLBContext)
          (pure (tlbcontext))))
  else
    (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
    (pure (tlbcontext)))


def AArch64_S1TTBR (regime : Regime) (va : (BitVec 64)) : SailM (BitVec 128) := do
  let varange : VARange := (AArch64_GetVARange va)
  match regime with
  | .Regime_EL3 =>
    (do
      let w__0 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
      (pure ((Sail.BitVec.zeroExtend w__0 128))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
      (pure ((Sail.BitVec.zeroExtend w__1 128))))
  | .Regime_EL20 =>
    (do
      if ((BEq.beq varange VARange_LOWER) : Bool)
      then
        (do
          let w__2 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
          (pure ((Sail.BitVec.zeroExtend w__2 128))))
      else
        (do
          let w__3 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
          (pure ((Sail.BitVec.zeroExtend w__3 128)))))
  | .Regime_EL10 =>
    (do
      if ((BEq.beq varange VARange_LOWER) : Bool)
      then
        (do
          let w__5 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
          (pure ((Sail.BitVec.zeroExtend w__5 128))))
      else
        (do
          let w__6 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
          (pure ((Sail.BitVec.zeroExtend w__6 128)))))
  | _ =>
    (do
      (undefined_bitvector_at (← occLabel 1480) 128))


/-- Type quantifiers: k_N : Nat, k_s2fs1mro : Bool, k_N ≥ 0 -/
def AArch64_S1NextWalkStateLeaf (currentstate : TTWState) (s2fs1mro : Bool) (regime : Regime) (ss : SecurityState) (walkparams : S1TTWParams) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let nextstate ← (( do (undefined_TTWState (← occLabel 1486) ()) ) : SailM TTWState )
  let baseaddress ← (( do (undefined_FullAddress (← occLabel 1487) ()) ) : SailM FullAddress )
  let w__0 ← (( do
    (AArch64_LeafBase descriptor walkparams.d128 walkparams.ds walkparams.tgx currentstate.level) )
    : SailM (BitVec 56) )
  let baseaddress := ({ baseaddress with address := w__0 } : FullAddress)
  let baseaddress ← (( do
    if ((BEq.beq currentstate.baseaddress.paspace PAS_Secure) : Bool)
    then
      (do
        let ns ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25426.39-25426.40"
              (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 127)])))))
          else
            (do
              ArmFull.assert (5 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25429.37-25429.38"
              (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 5)]))))) ) : SailM
          (BitVec 1) )
        let baseaddress : FullAddress :=
          { baseaddress with paspace := if ((ns == 0#1) : Bool)
            then PAS_Secure
            else PAS_NonSecure }
        (pure (baseaddress)))
    else
      (do
        if ((BEq.beq currentstate.baseaddress.paspace PAS_Root) : Bool)
        then
          (do
            let nse ← (( do (undefined_bitvector_at (← occLabel 1488) 1) ) : SailM (BitVec 1) )
            let ns ← (( do (undefined_bitvector_at (← occLabel 1489) 1) ) : SailM (BitVec 1) )
            let split_vec ← (( do
              if ((walkparams.d128 == 1#1) : Bool)
              then
                (do
                  ArmFull.assert (11 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25437.38-25437.39"
                  ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25438.39-25438.40"
                  (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 127)]))))))
              else
                (do
                  ArmFull.assert (11 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25441.38-25441.39"
                  (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 5)])))))) ) : SailM (BitVec (1 + 1)) )
            let nse : (BitVec 1) := (Sail.BitVec.extractLsb split_vec 1 1)
            let ns : (BitVec 1) := (Sail.BitVec.extractLsb split_vec 0 0)
            let w__1 ← (( do (DecodePASpace nse ns) ) : SailM PASpace )
            let baseaddress := ({ baseaddress with paspace := w__1 } : FullAddress)
            let w__3 ← (( do
              if (((BEq.beq baseaddress.paspace PAS_Secure) : Bool) : Bool)
              then
                (do
                  let w__2 ← (( do (HaveSecureState ()) ) : SailM Bool )
                  (pure (((! w__2) : Bool))))
              else (pure false) ) : SailM Bool )
            let baseaddress : FullAddress :=
              if (w__3 : Bool)
              then { baseaddress with paspace := PAS_NonSecure }
              else baseaddress
            (pure (baseaddress)))
        else
          (do
            if (((BEq.beq currentstate.baseaddress.paspace PAS_Realm) && ((BEq.beq regime Regime_EL2) || (BEq.beq
                     regime Regime_EL20))) : Bool)
            then
              (do
                let ns ← (( do
                  if ((walkparams.d128 == 1#1) : Bool)
                  then
                    (do
                      ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25451.39-25451.40"
                      (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 127)])))))
                  else
                    (do
                      ArmFull.assert (5 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25454.37-25454.38"
                      (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 5)]))))) )
                  : SailM (BitVec 1) )
                let baseaddress : FullAddress :=
                  { baseaddress with paspace := if ((ns == 0#1) : Bool)
                    then PAS_Realm
                    else PAS_NonSecure }
                (pure (baseaddress)))
            else
              (let baseaddress : FullAddress :=
                if ((BEq.beq currentstate.baseaddress.paspace PAS_Realm) : Bool)
                then { baseaddress with paspace := PAS_Realm }
                else { baseaddress with paspace := PAS_NonSecure }
              (pure (baseaddress))))) ) : SailM FullAddress )
  let nextstate : TTWState := { nextstate with istable := false }
  let nextstate : TTWState := { nextstate with level := currentstate.level }
  let nextstate : TTWState := { nextstate with baseaddress := baseaddress }
  let attrindx ← (( do (undefined_bitvector_at (← occLabel 1490) 4) ) : SailM (BitVec 4) )
  let attrindx ← (( do
    if ((walkparams.aie == 1#1) : Bool)
    then
      (do
        if ((walkparams.d128 == 1#1) : Bool)
        then
          (do
            ArmFull.assert (5 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25469.37-25469.38"
            let attrindx : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 5 2)
            (pure (attrindx)))
        else
          (do
            ArmFull.assert (59 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25472.38-25472.39"
            let attrindx : (BitVec 4) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 59)])) +++ (Sail.BitVec.extractLsb
                  descriptor 4 2))
            (pure (attrindx))))
    else
      (do
        ArmFull.assert (4 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25476.33-25476.34"
        let attrindx : (BitVec 4) := (0#1 +++ (Sail.BitVec.extractLsb descriptor 4 2))
        (pure (attrindx))) ) : SailM (BitVec 4) )
  let sh ← (( do (undefined_bitvector_at (← occLabel 1491) 2) ) : SailM (BitVec 2) )
  let sh ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25481.33-25481.34"
        let sh : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 9 8)
        (pure (sh)))
    else
      (do
        if ((walkparams.ds == 1#1) : Bool)
        then
          (let sh : (BitVec 2) := walkparams.sh
          (pure (sh)))
        else
          (do
            ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25486.33-25486.34"
            let sh : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 9 8)
            (pure (sh)))) ) : SailM (BitVec 2) )
  let attr ← (( do (AArch64_MAIRAttr (BitVec.toNat attrindx) walkparams.mair2 walkparams.mair) ) :
    SailM (BitVec 8) )
  let s1aarch64 : Bool := true
  let w__4 ← (( do (S1DecodeMemAttrs attr sh s1aarch64 walkparams) ) : SailM MemoryAttributes )
  let nextstate := ({ nextstate with memattrs := w__4 } : TTWState)
  let w__5 ← (( do
    (AArch64_S1ApplyOutputPerms currentstate.permissions descriptor regime walkparams) ) : SailM
    Permissions )
  let nextstate := ({ nextstate with permissions := w__5 } : TTWState)
  let protectedbit ← (( do (undefined_bitvector_at (← occLabel 1492) 1) ) : SailM (BitVec 1) )
  let protectedbit ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (114 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25495.35-25495.36"
        let protectedbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 114)]))
        (pure (protectedbit)))
    else
      (do
        if ((walkparams.pnch == 1#1) : Bool)
        then
          (do
            ArmFull.assert (52 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25499.38-25499.39"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 52)])))))
        else (pure (0#1))) ) : SailM (BitVec 1) )
  let nextstate : TTWState :=
    if (((currentstate.s1assured && s2fs1mro) && (protectedbit == 1#1)) : Bool)
    then { nextstate with s1assured := true }
    else { nextstate with s1assured := false }
  let nextstate ← (( do
    if (((walkparams.pnch == 1#1) || (currentstate.disch == 1#1)) : Bool)
    then
      (let nextstate : TTWState := { nextstate with contiguous := 0#1 }
      (pure (nextstate)))
    else
      (do
        ArmFull.assert (52 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25511.34-25511.35"
        let w__7 ← (( do
          (AArch64_ContiguousBit walkparams.tgx walkparams.d128 currentstate.level descriptor) ) :
          SailM (BitVec 1) )
        let nextstate := ({ nextstate with contiguous := w__7 } : TTWState)
        (pure (nextstate))) ) : SailM TTWState )
  let nextstate ← (( do
    if ((! (HasUnprivileged regime)) : Bool)
    then
      (let nextstate : TTWState := { nextstate with nG := 0#1 }
      (pure (nextstate)))
    else
      (do
        if (((BEq.beq ss SS_Secure) && (BEq.beq currentstate.baseaddress.paspace PAS_NonSecure)) : Bool)
        then
          (let nextstate : TTWState := { nextstate with nG := 1#1 }
          (pure (nextstate)))
        else
          (do
            ArmFull.assert (11 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25519.34-25519.35"
            let nextstate : TTWState :=
              { nextstate with nG := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)])) }
            (pure (nextstate)))) ) : SailM TTWState )
  if ((walkparams.d128 == 1#1) : Bool)
  then
    (do
      ArmFull.assert (113 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25523.35-25523.36"
      let nextstate : TTWState :=
        { nextstate with guardedpage := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor
              113)])) }
      (pure (nextstate)))
  else
    (do
      ArmFull.assert (50 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25526.34-25526.35"
      let nextstate : TTWState :=
        { nextstate with guardedpage := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor
              50)])) }
      (pure (nextstate)))


end ArmFull.Functions
