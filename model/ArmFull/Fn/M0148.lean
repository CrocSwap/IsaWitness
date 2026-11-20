module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0099
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0124 set_option backward.proofsInPublic true @[expose] public section

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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36001.65-36001.66"
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36028.65-36028.66"
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36055.65-36055.66"
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36081.65-36081.66"
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
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:36107.46-36107.47"
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
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:36147.46-36147.47"
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


def AArch32_ReportedInnerAttrs (attrs : (BitVec 3)) : SailM (BitVec 3) := do
  (__UNKNOWN_bits 3)


def AArch32_ReportedOuterAttrs (attrs : (BitVec 2)) : SailM (BitVec 2) := do
  (__UNKNOWN_bits 2)


/-- Type quantifiers: k_N : Nat, amount : Int, k_N ≥ 0 -/
def Shift_C (value_name : (BitVec k_N)) (srtype : SRType) (amount : Int) (carry_in : (BitVec 1)) : SailM ((BitVec k_N) × (BitVec 1)) := do
  ArmFull.assert (! ((BEq.beq srtype SRType_RRX) && (amount != 1))) "sail-inputs/03-v8_base.sail:41284.55-41284.56"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2695)
      (Sail.BitVec.length value_name))) ) : SailM (BitVec k_N) )
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 2696) 1) ) : SailM (BitVec 1) )
  let (carry_out, result) ← (( do
    if ((amount == 0) : Bool)
    then
      (let (tup__0, tup__1) := ((value_name, carry_in) : ((BitVec k_N) × (BitVec 1)))
      let result : (BitVec k_N) := tup__0
      let carry_out : (BitVec 1) := tup__1
      (pure ((carry_out, result))))
    else
      (do
        match srtype with
        | .SRType_LSL =>
          (let (tup__0, tup__1) := ((LSL_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
          let result : (BitVec k_N) := tup__0
          let carry_out : (BitVec 1) := tup__1
          (pure ((carry_out, result))))
        | .SRType_LSR =>
          (let (tup__0, tup__1) := ((LSR_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
          let result : (BitVec k_N) := tup__0
          let carry_out : (BitVec 1) := tup__1
          (pure ((carry_out, result))))
        | .SRType_ASR =>
          (do
            ArmFull.assert (((Sail.BitVec.length value_name) ≥b 0) && (amount ≥b 0)) "sail-inputs/03-v8_base.sail:41298.57-41298.58"
            let (tup__0, tup__1) :=
              ((ASR_C value_name (Sail.Int.toNatChecked (amount))) : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure ((carry_out, result))))
        | .SRType_ROR =>
          (do
            ArmFull.assert ((Sail.BitVec.length value_name) >b 0) "sail-inputs/03-v8_base.sail:41302.39-41302.40"
            let w__0 ← (( do (ROR_C value_name amount) ) : SailM ((BitVec k_N) × (BitVec 1)) )
            let (tup__0, tup__1) := (w__0 : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure ((carry_out, result))))
        | .SRType_RRX =>
          (do
            ArmFull.assert ((Sail.BitVec.length value_name) >b 1) "sail-inputs/03-v8_base.sail:41306.39-41306.40"
            let (tup__0, tup__1) := ((RRX_C value_name carry_in) : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure ((carry_out, result))))) ) : SailM ((BitVec 1) × (BitVec k_N)) )
  (pure ((result, carry_out)))


def T32ExpandImm (imm12 : (BitVec 12)) : SailM (BitVec 32) := do
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 2707) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (__tup_0, _) ← (( do (T32ExpandImm_C imm12 w__0.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  (pure (__tup_0))


def StandardFPSCRValue (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  let value_name : (BitVec 32) :=
    ((((0b00000#5 +++ (_get_FPSCR_Type_AHP w__0)) +++ 0b110000#6) +++ (_get_FPSCR_Type_FZ16 w__1)) +++ 0b0000000000000000000#19)
  (pure ((Mk_FPCRType (Sail.BitVec.zeroExtend value_name 64))))


/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def UnsignedSat (i : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2768)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (UnsignedSatQ i N)) ) : SailM
    ((BitVec N) × Bool) )
  (pure ((Sail.BitVec.castWidth __tup_0)))


/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def SignedSat (i : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2769)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ i N)) ) : SailM
    ((BitVec N) × Bool) )
  (pure ((Sail.BitVec.castWidth __tup_0)))


def AArch32_DTLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43624.65-43624.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2797) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
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


def AArch32_DTLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43642.65-43642.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2798) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_DTLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43662.65-43662.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2799) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DVA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros
          (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


end ArmFull.Functions
