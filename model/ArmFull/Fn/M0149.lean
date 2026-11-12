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
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0024
import ArmFull.Fn.M0039
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0050
import ArmFull.Fn.M0056
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0115
import ArmFull.Fn.M0121
import ArmFull.Fn.M0123
import ArmFull.Fn.M0124

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

/-- Type quantifiers: k_cold : Bool -/
def __Reset (cold : Bool) : SailM Unit := do
  writeReg __last_cycle_count 0
  writeReg __last_branch_valid false
  writeReg sp_rel_access_pc (Ones (n := 64))
  writeReg __cycle_count 0


/-- Type quantifiers: k_conditional : Bool, k_taken : Bool -/
def SPESampleAddOpOther (conditional : Bool) (taken : Bool) : SailM Unit := do
  let w__0 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  writeReg SPESampleEvents (BitVec.update w__0 6
    (Bit
      (if ((conditional && (! taken)) : Bool)
      then 1#1
      else 0#1)))
  (SPESampleAddOpOther__1 conditional)


/-- Type quantifiers: k_N : Nat, List.elem k_N [8, 16, 32, 64] -/
def SPEAddPacketToRecord (header_hi : (BitVec 2)) (header_lo : (BitVec 4)) (payload : (BitVec k_N)) : SailM Unit := do
  ArmFull.assert ((Nat.mod (Sail.BitVec.length payload) 8) == 0) "sail-arm/v8_base.sail:35115.26-35115.27"
  let sz ← (( do (undefined_bitvector_at (← occLabel 2436) 2) ) : SailM (BitVec 2) )
  let sz ← (( do
    match (Sail.BitVec.length payload) with
    | 8 => (pure (0b00#2))
    | 16 => (pure (0b01#2))
    | 32 => (pure (0b10#2))
    | 64 => (pure (0b11#2))
    | _ =>
      (do
        (Unreachable ())
        (pure (sz))) ) : SailM (BitVec 2) )
  let header : (BitVec 8) := ((header_hi +++ sz) +++ header_lo)
  (SPEAddByteToRecord header)
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat :=
    (Sail.Int.toNatChecked (((Int.ediv (Sail.BitVec.length payload) 8) -i 1)))
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (SPEAddByteToRecord
          (Sail.BitVec.castWidth (Sail.BitVec.extractLsb payload
            (Sail.Int.toNatChecked (((i *i 8) +i 7))) (Sail.Int.toNatChecked ((i *i 8))))))
    (pure loop_vars))


def AArch64_TLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:35915.46-35915.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2461) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ALL }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_VMALL (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-arm/v8_base.sail:35933.65-35933.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2462) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALL }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_VMALLS12 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:35952.46-35952.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2463) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALLS12 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-arm/v8_base.sail:35971.65-35971.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2464) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ASID }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-arm/v8_base.sail:35991.65-35991.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2465) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord :=
    { r with address := (Sail.BitVec.zeroExtend
        ((Sail.BitVec.extractLsb Xt 43 0) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord := { r with d64 := true }
  let b__0 := r.ttl
  let r : TLBIRecord :=
    { r with d128 := (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBIP_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-arm/v8_base.sail:36018.65-36018.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2466) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord :=
    { r with address := (Sail.BitVec.zeroExtend
        ((Sail.BitVec.extractLsb Xt 107 64) +++ (Zeros (n := 12))) 64) }
  let b__0 := r.ttl
  let r : TLBIRecord :=
    { r with d64 := (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r : TLBIRecord := { r with d128 := true }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-arm/v8_base.sail:36045.65-36045.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2467) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord :=
    { r with address := (Sail.BitVec.zeroExtend
        ((Sail.BitVec.extractLsb Xt 43 0) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord := { r with d64 := true }
  let b__0 := r.ttl
  let r : TLBIRecord :=
    { r with d128 := (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBIP_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-arm/v8_base.sail:36071.65-36071.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2468) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord :=
    { r with address := (Sail.BitVec.zeroExtend
        ((Sail.BitVec.extractLsb Xt 107 64) +++ (Zeros (n := 12))) 64) }
  let b__0 := r.ttl
  let r : TLBIRecord :=
    { r with d64 := (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r : TLBIRecord := { r with d128 := true }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:36097.46-36097.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2469) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord :=
    { r with address := (Sail.BitVec.zeroExtend
        ((Sail.BitVec.extractLsb Xt 39 0) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord := { r with d64 := true }
  let b__0 := r.ttl
  let r : TLBIRecord :=
    { r with d128 := (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
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
  (pure (()))


def AArch64_TLBIP_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:36137.46-36137.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2470) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord :=
    { r with address := (Sail.BitVec.zeroExtend
        ((Sail.BitVec.extractLsb Xt 107 64) +++ (Zeros (n := 12))) 64) }
  let b__0 := r.ttl
  let r : TLBIRecord :=
    { r with d64 := (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r : TLBIRecord := { r with d128 := true }
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
  (pure (()))


def TLBIPRange (regime : Regime) (Xt : (BitVec 128)) : SailM (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) := do
  let valid_name : Bool := true
  let start_address : (BitVec 64) := (Zeros (n := 64))
  let end_address_name : (BitVec 64) := (Zeros (n := 64))
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let tg_bits : Int := 12
  if ((tg == 0b00#2) : Bool)
  then (pure ((false, tg, start_address, end_address_name)))
  else
    (do
      let (start_address, tg_bits) ← (( do
        match tg with
        | 0b01 =>
          (let tg_bits : Int := 12
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 55 12 (Sail.BitVec.extractLsb Xt 107 64))
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 63 56
              (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 107)])) 8))
          (pure ((start_address, tg_bits))))
        | 0b10 =>
          (let tg_bits : Int := 14
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 55 14 (Sail.BitVec.extractLsb Xt 107 66))
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 63 56
              (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 107)])) 8))
          (pure ((start_address, tg_bits))))
        | 0b11 =>
          (let tg_bits : Int := 16
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 55 16 (Sail.BitVec.extractLsb Xt 107 68))
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 63 56
              (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 107)])) 8))
          (pure ((start_address, tg_bits))))
        | _ =>
          (do
            (Unreachable ())
            (pure ((start_address, tg_bits)))) ) : SailM ((BitVec 64) × Int) )
      let tg_bits : Int := tg_bits
      let range : Int :=
        (Int.shiftl (num +i 1) (Sail.Int.toNatChecked ((((5 *i scale) +i 1) +i tg_bits))))
      let end_address_name : (BitVec 64) :=
        (start_address + (Sail.BitVec.castWidth (m := 64) (integer_subrange range 63 0)))
      let end_address_name : (BitVec 64) :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access end_address_name 55)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 start_address 55)]))) : Bool)
        then
          ((BitVec.replicateBits
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access start_address 55)]))
              (Sail.Int.toNatChecked ((64 -i 55)))) +++ (Ones (n := 55)))
        else end_address_name
      (pure ((valid_name, tg, start_address, end_address_name))))


def AArch32_GetS2TTWParams (_ : Unit) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 2535) ()) ) : SailM S2TTWParams )
  let walkparams : S2TTWParams := { walkparams with tgx := TGx_4KB }
  let w__0 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with s := (_get_VTCR_Type_S w__0) } : S2TTWParams)
  let w__1 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with t0sz := (_get_VTCR_Type_T0SZ w__1) } : S2TTWParams)
  let w__2 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with sl0 := (_get_VTCR_Type_SL0 w__2) } : S2TTWParams)
  let w__3 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with irgn := (_get_VTCR_Type_IRGN0 w__3) } : S2TTWParams)
  let w__4 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with orgn := (_get_VTCR_Type_ORGN0 w__4) } : S2TTWParams)
  let w__5 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with sh := (_get_VTCR_Type_SH0 w__5) } : S2TTWParams)
  let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with ee := (_get_HSCTLR_Type_EE w__6) } : S2TTWParams)
  let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with ptw := (_get_HCR_Type_PTW w__7) } : S2TTWParams)
  let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let w__9 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let walkparams :=
    ({ walkparams with vm := ((_get_HCR_Type_VM w__8) ||| (_get_HCR_Type_DC w__9)) } : S2TTWParams)
  if ((walkparams.s != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access walkparams.t0sz 3)]))) : Bool)
  then
    (do
      let low ← (( do (undefined_bitvector_at (← occLabel 2536) 3) ) : SailM (BitVec 3) )
      let __tup_1 : (BitVec 4) := (walkparams.s +++ low)
      let walkparams : S2TTWParams := { walkparams with t0sz := __tup_1 }
      (pure (walkparams)))
  else (pure (walkparams))


def AArch32_SDStageOA (baseaddress : FullAddress) (va : (BitVec 32)) (sdftype : SDFType) : SailM FullAddress := do
  let tsize : Int := 12
  let tsize : Int :=
    match sdftype with
    | .SDFType_SmallPage => 12
    | .SDFType_LargePage => 16
    | .SDFType_Section => 20
    | .SDFType_Supersection => 24
    | _ => tsize
  let tsize : Int := tsize
  let oa ← (( do (undefined_FullAddress (← occLabel 2631) ()) ) : SailM FullAddress )
  let oa : FullAddress :=
    { oa with address := (Sail.BitVec.castWidth (m := 56) ((Sail.BitVec.extractLsb
          baseaddress.address 55 (Sail.Int.toNatChecked (tsize))) +++ (Sail.BitVec.extractLsb va
          (Sail.Int.toNatChecked ((tsize -i 1))) 0))) }
  let oa : FullAddress := { oa with paspace := baseaddress.paspace }
  (pure (oa))


def ReportedPARAttrs (parattrs : (BitVec 8)) : SailM (BitVec 8) := do
  (__UNKNOWN_bits 8)


def ReportedPARShareability (sh : (BitVec 2)) : SailM (BitVec 2) := do
  (__UNKNOWN_bits 2)


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV83 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap3_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV82 enabled))
  else (pure (()))


def AArch32_PARFaultStatusSD (fault : FaultRecord) : SailM (BitVec 6) := do
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 2685) 6) ) : SailM (BitVec 6) )
  let w__0 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let w__1 : (BitVec 1) :=
    if (w__0 : Bool)
    then fault.extflag
    else 0#1
  let syndrome := ((BitVec.update syndrome 5 (Bit w__1)) : (BitVec 6))
  let w__2 ← (( do (EncodeSDFSC fault.statuscode fault.level) ) : SailM (BitVec 5) )
  let syndrome := ((Sail.BitVec.updateSubrange syndrome 4 0 w__2) : (BitVec 6))
  (pure (syndrome))


def AArch32_PAROuterAttrs (memattrs : MemoryAttributes) : SailM (BitVec 2) := do
  let result ← (( do (undefined_bitvector_at (← occLabel 2687) 2) ) : SailM (BitVec 2) )
  if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
  then
    (do
      (__UNKNOWN_bits 2))
  else
    (let outer : MemAttrHints := memattrs.outer
    let result : (BitVec 2) :=
      if ((outer.attrs == MemAttr_NC) : Bool)
      then 0b00#2
      else
        (if (((outer.attrs == MemAttr_WB) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   outer.hints 0)])) == 1#1)) : Bool)
        then 0b01#2
        else
          (if (((outer.attrs == MemAttr_WT) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     outer.hints 0)])) == 0#1)) : Bool)
          then 0b10#2
          else
            (if (((outer.attrs == MemAttr_WB) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       outer.hints 0)])) == 0#1)) : Bool)
            then 0b11#2
            else result)))
    (pure (result)))


end ArmFull.Functions
