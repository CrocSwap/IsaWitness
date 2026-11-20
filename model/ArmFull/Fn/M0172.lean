module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0080
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0138
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0170 set_option backward.proofsInPublic true @[expose] public section

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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36363.65-36363.66"
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36425.65-36425.66"
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
      ArmFull.assert ((fault.level == 1) || (fault.level == 2)) "sail-inputs/03-v8_base.sail:39076.50-39076.51"
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
      ArmFull.assert ((fault.level == 1) || (fault.level == 2)) "sail-inputs/03-v8_base.sail:41018.50-41018.51"
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
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:42371.80-42371.81"
  ArmFull.assert ((BEq.beq iset InstrSet_A32) || (BEq.beq iset InstrSet_T32)) "sail-inputs/03-v8_base.sail:42372.54-42372.55"
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with T := if ((BEq.beq iset InstrSet_A32) : Bool)
    then 0#1
    else 1#1 }


def InITBlock (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  if ((BEq.beq w__0 InstrSet_T32) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (pure (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb w__1.IT 3 0)) != 0b0000#4))))
  else (pure (false))


def SPSRWriteByInstr (value_name : (BitVec 32)) (bytemask : (BitVec 4)) : SailM Unit := do
  let new_spsr ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 3)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 31 24 (Sail.BitVec.extractLsb value_name 31 24))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 2)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 23 16 (Sail.BitVec.extractLsb value_name 23 16))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 1)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 15 8 (Sail.BitVec.extractLsb value_name 15 8))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 0)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 7 0 (Sail.BitVec.extractLsb value_name 7 0))
    else new_spsr
  (SPSR_set (N := 32) new_spsr)


/-- Type quantifiers: t : Int -/
def RMR_EL1_SysRegRead_9adb359c4ff7cc32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL1) : Bool)))) : Bool)
    then
      (do
        (IsHighestEL EL1))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
      (X_set t 64 (__get_RMR_EL1 w__3)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RMR_EL3_SysRegRead_412ca53e076c7a6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then
      (do
        (IsHighestEL EL3))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      (X_set t 64 (__get_RMR_EL3 w__3)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RVBAR_EL1_SysRegRead_c839c12def98ebc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL1) : Bool)))) : Bool)
    then
      (do
        (IsHighestEL EL1))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg RVBAR_EL1 ) : SailM (BitVec 64) )
      (X_set t 64 w__3))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RVBAR_EL3_SysRegRead_d57b9abefb0ea569 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then
      (do
        (IsHighestEL EL3))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg RVBAR_EL3 ) : SailM (BitVec 64) )
      (X_set t 64 w__3))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENCLR0_EL0_SysRegWrite_87e21241643a862e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR0_EL0 (Mk_AMCNTENCLR0_EL0_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_EL0_SysRegWrite_c63fb61a666d3a21 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR1_EL0 (Mk_AMCNTENCLR1_EL0_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENSET0_EL0_SysRegWrite_b4e12b5dd3b0738a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENSET0_EL0 (Mk_AMCNTENSET0_EL0_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENSET1_EL0_SysRegWrite_a3bee0219e2d4b9e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENSET1_EL0 (Mk_AMCNTENSET1_EL0_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCR_EL0_SysRegWrite_6a9019dd97aa8af1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCR_EL0 (Mk_AMCR_EL0_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_57776cdcd88bec7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 2 (Mk_AMEVCNTR0_EL0_Type w__2)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_a28bd21dde7b55b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 1 (Mk_AMEVCNTR0_EL0_Type w__2)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_ca5a4224a458ea03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 0 (Mk_AMEVCNTR0_EL0_Type w__2)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_df6bb2663cab03ed (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 3 (Mk_AMEVCNTR0_EL0_Type w__2)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_2bb86c4004ef9258 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 0 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_2cb2cddc132a8d44 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 6 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_3743486d55da4508 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 1 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_44cf3260f4372341 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 5 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_4a152435dd65137a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 10 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


end ArmFull.Functions
