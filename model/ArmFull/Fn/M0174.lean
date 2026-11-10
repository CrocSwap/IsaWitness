import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0046
import ArmFull.Fn.M0061
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0169

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

def DebugWriteExternalAbort (memstatus : PhysMemRetStatus) (addrdesc : AddressDescriptor) (start_vaddr : (BitVec 64)) : SailM Unit := do
  let iswrite : Bool := true
  let handle_as_SError : Bool := false
  let async_external_abort : Bool := false
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 2437) 64) ) : SailM (BitVec 64) )
  let (async_external_abort, handle_as_SError, syndrome) ← (( do
    match addrdesc.fault.access.acctype with
    | .AccessType_SPE =>
      (do
        let w__0 ← (( do (__IMPDEF_boolean "SPE SyncExternal as SError") ) : SailM Bool )
        let handle_as_SError := (w__0 : Bool)
        let w__1 ← (( do (__IMPDEF_boolean "SPE async External abort") ) : SailM Bool )
        let async_external_abort := (w__1 : Bool)
        let w__2 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
        let syndrome := ((Sail.BitVec.extractLsb w__2 63 0) : (BitVec 64))
        (pure ((async_external_abort, handle_as_SError, syndrome))))
    | _ =>
      (do
        (Unreachable ())
        (pure ((async_external_abort, handle_as_SError, syndrome)))) ) : SailM
    (Bool × Bool × (BitVec 64)) )
  let ttw_abort : Bool :=
    ((BEq.beq addrdesc.fault.statuscode Fault_SyncExternalOnWalk) || (BEq.beq
        addrdesc.fault.statuscode Fault_SyncParityOnWalk))
  let statuscode : Fault :=
    if (ttw_abort : Bool)
    then addrdesc.fault.statuscode
    else memstatus.statuscode
  let extflag : (BitVec 1) :=
    if (ttw_abort : Bool)
    then addrdesc.fault.extflag
    else memstatus.extflag
  if ((((BEq.beq statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity)) || handle_as_SError) : Bool)
  then
    (do
      let fault ← (( do (NoFault ()) ) : SailM FaultRecord )
      let parity : Bool :=
        ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq statuscode Fault_AsyncParity) || (BEq.beq
              statuscode Fault_SyncParityOnWalk)))
      let fault : FaultRecord :=
        { fault with statuscode := if (parity : Bool)
          then Fault_AsyncParity
          else Fault_AsyncExternal }
      let w__3 ← (( do (HaveRASExt ()) ) : SailM Bool )
      let fault : FaultRecord :=
        if (w__3 : Bool)
        then { fault with merrorstate := memstatus.merrorstate }
        else fault
      let fault : FaultRecord := { fault with extflag := extflag }
      let fault : FaultRecord :=
        { fault with access := { fault.access with acctype := addrdesc.fault.access.acctype } }
      (pure ((PendSErrorInterrupt fault))))
  else
    (do
      let syndrome : (BitVec 64) := (BitVec.update syndrome 18 (Bit 1#1))
      let syndrome : (BitVec 64) :=
        if (((BEq.beq addrdesc.fault.access.acctype AccessType_SPE) && (async_external_abort || (start_vaddr != addrdesc.vaddress))) : Bool)
        then (BitVec.update syndrome 19 (Bit 1#1))
        else syndrome
      let syndrome ← (( do
        if ((IsZero (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access syndrome 17)]))) : Bool)
        then
          (do
            let syndrome : (BitVec 64) := (BitVec.update syndrome 17 (Bit 1#1))
            let ec ← (( do (undefined_bitvector_at (← occLabel 2438) 6) ) : SailM (BitVec 6) )
            let w__6 ← (( do
              (pure ((← do
                    (pure ((← do
                          (HaveRME ())) && ((bne addrdesc.fault.gpcf.gpf GPCF_None) : Bool)))) && ((bne
                    addrdesc.fault.gpcf.gpf GPCF_Fail) : Bool))) ) : SailM Bool )
            let ec : (BitVec 6) :=
              if (w__6 : Bool)
              then 0b011110#6
              else
                (if (addrdesc.fault.secondstage : Bool)
                then 0b100101#6
                else 0b100100#6)
            let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 31 26 ec)
            if (async_external_abort : Bool)
            then
              (let syndrome : (BitVec 64) :=
                (Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ 0b010001#6))
              (pure (syndrome)))
            else
              (do
                let w__7 ← (( do (EncodeLDFSC statuscode addrdesc.fault.level) ) : SailM
                  (BitVec 6) )
                let syndrome :=
                  ((Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ w__7)) : (BitVec 64))
                (pure (syndrome))))
        else (pure (syndrome)) ) : SailM (BitVec 64) )
      match addrdesc.fault.access.acctype with
      | .AccessType_SPE =>
        (do
          let w__8 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
          writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__8 63 0 syndrome))
      | _ =>
        (do
          (Unreachable ())))


def DebugWriteFault (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 2439) 64) ) : SailM (BitVec 64) )
  let syndrome ← (( do
    match fault.access.acctype with
    | .AccessType_SPE =>
      (do
        let w__0 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
        let syndrome := ((Sail.BitVec.extractLsb w__0 63 0) : (BitVec 64))
        (pure (syndrome)))
    | _ =>
      (do
        (Unreachable ())
        (pure (syndrome))) ) : SailM (BitVec 64) )
  let w__1 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
  let syndrome :=
    ((Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ w__1)) : (BitVec 64))
  let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 55 32 (Zeros (n := 24)))
  let ec ← (( do (undefined_bitvector_at (← occLabel 2440) 6) ) : SailM (BitVec 6) )
  let w__4 ← (( do
    (pure ((← do
          (pure ((← do
                (HaveRME ())) && ((bne fault.gpcf.gpf GPCF_None) : Bool)))) && ((bne fault.gpcf.gpf
          GPCF_Fail) : Bool))) ) : SailM Bool )
  let ec : (BitVec 6) :=
    if (w__4 : Bool)
    then 0b011110#6
    else
      (if (fault.secondstage : Bool)
      then 0b100101#6
      else 0b100100#6)
  let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 31 26 ec)
  let syndrome : (BitVec 64) := (BitVec.update syndrome 17 (Bit 1#1))
  let syndrome : (BitVec 64) :=
    if ((BEq.beq fault.statuscode Fault_Permission) : Bool)
    then
      (let syndrome : (BitVec 64) :=
        (BitVec.update syndrome 39
          (Bit
            (if (fault.assuredonly : Bool)
            then 1#1
            else 0#1)))
      let syndrome : (BitVec 64) :=
        (BitVec.update syndrome 38
          (Bit
            (if (fault.overlay : Bool)
            then 1#1
            else 0#1)))
      (BitVec.update syndrome 37
        (Bit
          (if (fault.dirtybit : Bool)
          then 1#1
          else 0#1))))
    else syndrome
  match fault.access.acctype with
  | .AccessType_SPE =>
    (do
      let w__5 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__5 63 0 syndrome))
  | _ =>
    (do
      (Unreachable ()))


def BRBEBranchOnISB (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "ISB generates Branch records")


def AArch64_TLBI_RVA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36297.65-36297.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2472) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let valid_name ← (( do (undefined_bool_at (← occLabel 2473) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


def AArch64_TLBI_RVAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36353.65-36353.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2476) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr : Int := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool_at (← occLabel 2477) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


def AArch64_TLBI_RIPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36415.65-36415.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2480) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RIPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr : Int := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool_at (← occLabel 2481) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      let r ← (( do
        match security with
        | .SS_NonSecure =>
          (let r : TLBIRecord := { r with ipaspace := PAS_NonSecure }
          (pure (r)))
        | .SS_Secure =>
          (let r : TLBIRecord :=
            { r with ipaspace := if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 63)])) == 1#1) : Bool)
              then PAS_NonSecure
              else PAS_Secure }
          (pure (r)))
        | .SS_Realm =>
          (let r : TLBIRecord := { r with ipaspace := PAS_Realm }
          (pure (r)))
        | _ =>
          (do
            (Unreachable ())
            (pure (r))) ) : SailM TLBIRecord )
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


def AArch32_EL2Enabled (ss : SecurityState) : SailM Bool := do
  if ((BEq.beq ss SS_Secure) : Bool)
  then
    (do
      let w__1 ← (( do
        if (((HaveEL EL2) : Bool) : Bool)
        then
          (do
            (HaveSecureEL2Ext ()))
        else (pure false) ) : SailM Bool )
      if ((! w__1) : Bool)
      then (pure (false))
      else
        (do
          if ((HaveEL EL3) : Bool)
          then
            (do
              let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure (((_get_SCR_EL3_Type_EEL2 w__2) == 1#1))))
          else
            (do
              (__IMPDEF_boolean "Secure-only implementation"))))
  else (pure ((HaveEL EL2)))


def AArch32_DefaultTEXDecode (TEX_in : (BitVec 3)) (C_in : (BitVec 1)) (B_in : (BitVec 1)) (s : (BitVec 1)) : SailM MemoryAttributes := do
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2590) ()) ) : SailM
    MemoryAttributes )
  let TEX : (BitVec 3) := TEX_in
  let C : (BitVec 1) := C_in
  let B : (BitVec 1) := B_in
  let (B, C, TEX) ← (( do
    if (((((TEX == 0b001#3) && ((C +++ B) == 0b01#2)) || ((TEX == 0b010#3) && ((C +++ B) != 0b00#2))) || (TEX == 0b011#3)) : Bool)
    then
      (do
        let texcb ← (( do (undefined_bitvector_at (← occLabel 2591) 5) ) : SailM (BitVec 5) )
        let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_RESTEXCB 5) ) : SailM
          (Constraint × (BitVec 5)) )
        let texcb : (BitVec 5) := __tup_1
        let TEX : (BitVec 3) := (Sail.BitVec.extractLsb texcb 4 2)
        let C : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access texcb 1)]))
        let B : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access texcb 0)]))
        (pure ((B, C, TEX))))
    else (pure ((B, C, TEX))) ) : SailM ((BitVec 1) × (BitVec 1) × (BitVec 3)) )
  let memattrs ← (( do
    match (BitVec.setWidth 5 ((TEX +++ C) +++ B)) with
    | 0b00000 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
      let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRnE }
      let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
      (pure (memattrs)))
    | 0b00001 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
      let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRE }
      let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
      (pure (memattrs)))
    | 0b01000 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
      let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRE }
      let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
      (pure (memattrs)))
    | 0b00010 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with attrs := MemAttr_WT } }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with hints := MemHint_RA } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with attrs := MemAttr_WT } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with hints := MemHint_RA } }
      let memattrs : MemoryAttributes :=
        { memattrs with shareability := if ((s == 1#1) : Bool)
          then Shareability_OSH
          else Shareability_NSH }
      (pure (memattrs)))
    | 0b00011 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with attrs := MemAttr_WB } }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with hints := MemHint_RA } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with attrs := MemAttr_WB } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with hints := MemHint_RA } }
      let memattrs : MemoryAttributes :=
        { memattrs with shareability := if ((s == 1#1) : Bool)
          then Shareability_OSH
          else Shareability_NSH }
      (pure (memattrs)))
    | 0b00100 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with attrs := MemAttr_NC } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with attrs := MemAttr_NC } }
      let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
      (pure (memattrs)))
    | 0b00110 =>
      (do
        (__IMPDEF_MemoryAttributes ""))
    | 0b00111 =>
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with attrs := MemAttr_WB } }
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with hints := MemHint_RWA } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with attrs := MemAttr_WB } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with hints := MemHint_RWA } }
      let memattrs : MemoryAttributes :=
        { memattrs with shareability := if ((s == 1#1) : Bool)
          then Shareability_OSH
          else Shareability_NSH }
      (pure (memattrs)))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (1#1 : (BitVec 1))) : Bool)
        then
          (do
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let w__1 ← (( do (DecodeSDFAttr (C +++ B)) ) : SailM MemAttrHints )
            let memattrs := ({ memattrs with inner := w__1 } : MemoryAttributes)
            let w__2 ← (( do (DecodeSDFAttr (Sail.BitVec.extractLsb TEX 1 0)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with outer := w__2 } : MemoryAttributes)
            let memattrs : MemoryAttributes :=
              if (((memattrs.inner.attrs == MemAttr_NC) && (memattrs.outer.attrs == MemAttr_NC)) : Bool)
              then { memattrs with shareability := Shareability_OSH }
              else
                { memattrs with shareability := if ((s == 1#1) : Bool)
                  then Shareability_OSH
                  else Shareability_NSH }
            (pure (memattrs)))
        else
          (do
            (Unreachable ())
            (pure (memattrs)))) ) : SailM MemoryAttributes )
  let memattrs : MemoryAttributes :=
    { memattrs with inner := { memattrs.inner with transient := false } }
  let memattrs : MemoryAttributes :=
    { memattrs with outer := { memattrs.outer with transient := false } }
  let memattrs : MemoryAttributes := { memattrs with tags := MemTag_Untagged }
  let memattrs : MemoryAttributes :=
    if (((memattrs.inner.attrs == MemAttr_WB) && (memattrs.outer.attrs == MemAttr_WB)) : Bool)
    then { memattrs with xs := 0#1 }
    else { memattrs with xs := 1#1 }
  (pure (memattrs))


def AArch64_PARFaultStatus (fault : FaultRecord) : SailM (BitVec 6) := do
  let fst ← (( do (undefined_bitvector_at (← occLabel 2637) 6) ) : SailM (BitVec 6) )
  if ((BEq.beq fault.statuscode Fault_Domain) : Bool)
  then
    (do
      ArmFull.assert ((fault.level == 1) || (fault.level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:39066.50-39066.51"
      let fst : (BitVec 6) :=
        (Sail.BitVec.updateSubrange fst 1 0
          (if ((fault.level == 1) : Bool)
          then 0b01#2
          else 0b10#2))
      let fst : (BitVec 6) := (Sail.BitVec.updateSubrange fst 5 2 0b1111#4)
      (pure (fst)))
  else
    (do
      (EncodeLDFSC fault.statuscode fault.level))


def DBGDTR_EL0_read__1 (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _DBGDTR_EL0 ) : SailM DBGDTR_EL0_Type )
  let w__0 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
  let r ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
        let r := ((Sail.BitVec.updateSubrange r 63 32 (BitVec.slice w__1 0 32)) : (BitVec 64))
        (pure (r)))
    else
      (do
        let w__2 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
            let r := ((Sail.BitVec.updateSubrange r 63 32 (BitVec.slice w__3 0 32)) : (BitVec 64))
            (pure (r)))
        else
          (do
            let w__4 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
            let r := ((Sail.BitVec.updateSubrange r 63 32 (BitVec.slice w__4 0 32)) : (BitVec 64))
            (pure (r)))) ) : SailM (BitVec 64) )
  let w__5 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__6 0 32)) : (BitVec 64))
      (pure (r)))
  else
    (do
      let w__7 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__8 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__8 0 32)) : (BitVec 64))
          (pure (r)))
      else
        (do
          let w__9 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__9 0 32)) : (BitVec 64))
          (pure (r))))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV86 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap6_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV85 enabled))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV90 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap0_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV85 enabled))
  else (pure (()))


def AArch32_PARFaultStatusLD (fault : FaultRecord) : SailM (BitVec 6) := do
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 2683) 6) ) : SailM (BitVec 6) )
  if ((BEq.beq fault.statuscode Fault_Domain) : Bool)
  then
    (do
      ArmFull.assert ((fault.level == 1) || (fault.level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:41008.50-41008.51"
      let syndrome : (BitVec 6) :=
        (Sail.BitVec.updateSubrange syndrome 1 0
          (if ((fault.level == 1) : Bool)
          then 0b01#2
          else 0b10#2))
      let syndrome : (BitVec 6) := (Sail.BitVec.updateSubrange syndrome 5 2 0b1111#4)
      (pure (syndrome)))
  else
    (do
      (EncodeLDFSC fault.statuscode fault.level))


def SelectInstrSet (iset : InstrSet) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
         (pure (((BEq.beq w__0 InstrSet_A32) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
        (pure (((BEq.beq w__1 InstrSet_T32) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42361.80-42361.81"
  ArmFull.assert ((BEq.beq iset InstrSet_A32) || (BEq.beq iset InstrSet_T32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42362.54-42362.55"
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with T := if ((BEq.beq iset InstrSet_A32) : Bool)
    then 0#1
    else 1#1 }


end ArmFull.Functions
