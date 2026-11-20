module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0143 set_option backward.proofsInPublic true @[expose] public section

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

def AArch32_ITLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43683.65-43683.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2800) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IALL }
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


def AArch32_ITLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43701.65-43701.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2801) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IASID }
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


def AArch32_ITLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43721.65-43721.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2802) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IVA }
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


def AArch32_TLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:43742.46-43742.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2803) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ALL }
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


def AArch32_TLBI_VMALL (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43760.65-43760.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2804) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
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


def AArch32_TLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43779.65-43779.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2805) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ASID }
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


def AArch32_TLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43799.65-43799.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2806) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
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


def AArch32_TLBI_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43820.65-43820.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2807) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros
          (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:43840.46-43840.47"
  ArmFull.assert (BEq.beq security SS_NonSecure) "sail-inputs/03-v8_base.sail:43841.35-43841.36"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2808) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 24)) +++ (Sail.BitVec.extractLsb Rt 27 0)) +++ (Zeros
          (n := 12))) }
  let r : TLBIRecord := { r with ipaspace := PAS_NonSecure }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def __set_PMCR_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMCR_EL0_Type := value_name
  let w__0 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (BitVec.update w__0 0 (Bit (BitVec.slice r 0 1)))
  let w__1 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__1 15 3 (BitVec.slice r 3 13))
  let w__2 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__2 63 32 (BitVec.slice r 32 32))
  let w__3 ← (( do (IsFeatureImplemented FEAT_PMUv3p7) ) : SailM Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__4 31 24 (_get_PMCR_EL0_Type_IMP r)))
  else (pure (()))
  let w__5 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  if ((! ((_get_PMCR_EL0_Type_IMP w__5) != 0b00000000#8)) : Bool)
  then
    (do
      let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__6 23 16 (_get_PMCR_EL0_Type_IDCODE r)))
  else (pure (()))
  let w__7 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__7 2 2 (_get_PMCR_EL0_Type_C r))
  let w__8 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__8 1 1 (_get_PMCR_EL0_Type_P r))


def __set_MPAM3_EL3 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM3_EL3_Type := value_name
  let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 63 w__0 0 (BitVec.slice r 0 63))))
  let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_MPAMEN w__1 (_get_MPAM3_EL3_Type_MPAMEN r)))


def __set_PMCR (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCR_Type := value_name
  let w__0 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (Mk_PMCR_Type (set_slice 1 w__0 0 (BitVec.slice r 0 1))))
  let w__1 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (Mk_PMCR_Type (set_slice 13 w__1 3 (BitVec.slice r 3 13))))
  let w__2 ← (( do (IsFeatureImplemented FEAT_PMUv3p7) ) : SailM Bool )
  if ((! (! w__2)) : Bool)
  then
    (do
      let w__3 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
      (PMCR_write (_update_PMCR_Type_IMP w__3 (_get_PMCR_Type_IMP r))))
  else (pure (()))
  let w__4 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  if ((! ((_get_PMCR_Type_IMP w__4) != 0b00000000#8)) : Bool)
  then
    (do
      let w__5 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
      (PMCR_write (_update_PMCR_Type_IDCODE w__5 (_get_PMCR_Type_IDCODE r))))
  else (pure (()))
  let w__6 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_C w__6 (_get_PMCR_Type_C r)))
  let w__7 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_P w__7 (_get_PMCR_Type_P r)))


def __get_OSDLR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : OSDLR_EL1_Type := value_name
  let w__0 ← (( do (IsFeatureImplemented FEAT_DoubleLock) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_OSDLR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1#4 64)))))
    else tmp
  let tmp : OSDLR_EL1_Type :=
    (Mk_OSDLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))
  (pure (tmp))


def __get_DBGOSDLR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : DBGOSDLR_Type := value_name
  let w__0 ← (( do (IsFeatureImplemented FEAT_DoubleLock) ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_DBGOSDLR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1#4 32)))))
    else tmp
  let tmp : DBGOSDLR_Type := (Mk_DBGOSDLR_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))
  (pure (tmp))


def ChooseRandomNonExcludedTag (exclude_in : (BitVec 16)) : SailM (BitVec 4) := do
  (__UNKNOWN_bits 4)


def undefined_TLBIInfo (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBIInfo := do
  let w__0 ← (( do (undefined_TLBIRecord (ℓ.child 0) ()) ) : SailM TLBIRecord )
  let w__1 ← (( do (undefined_Shareability (ℓ.child 1) ()) ) : SailM Shareability )
  (pure ({ rec' := w__0
           shareability := w__1 }))


def __GIC_ClearPendingInterrupt (intid : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg __GIC_Pending ) : SailM (Option InterruptID) )
  match w__0 with
  | .some pending_intid =>
    (do
      if (((__GIC_InterruptID pending_intid) == intid) : Bool)
      then
        (do
          writeReg __GIC_Pending none)
      else (pure (())))
  | _ => (pure (()))


def HaveFP16Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FP16)


/-- Type quantifiers: k_data_cache : Bool, level : Int -/
def getCacheID (level : Int) (data_cache : Bool) : SailM (BitVec 64) := do
  let range_min : Int := (level *i 3)
  let w__0 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
  let cache_type : (BitVec 3) := (BitVec.slice w__0 (Sail.Int.toNatChecked (range_min)) 3)
  let ccsidr_val ← (( do (undefined_bitvector_at (← occLabel 2894) 64) ) : SailM (BitVec 64) )
  match cache_type with
  | 0b000 =>
    (do
      (__UNKNOWN_bits 64))
  | 0b001 =>
    (do
      if (data_cache : Bool)
      then
        (do
          (__UNKNOWN_bits 64))
      else
        (do
          ArmFull.assert ((0 ≤b level) && (level <b 7)) "sail-inputs/12-sysregs.sail:222.59-222.60"
          let w__3 ← (( do readReg __ICACHE_CCSIDR_RESET ) : SailM (Vector (BitVec 64) 7) )
          (pure ((GetElem?.getElem! w__3 (Sail.Int.toNatChecked (level)))))))
  | 0b010 =>
    (do
      if ((! data_cache) : Bool)
      then
        (do
          (__UNKNOWN_bits 64))
      else
        (do
          ArmFull.assert ((0 ≤b level) && (level <b 7)) "sail-inputs/12-sysregs.sail:228.59-228.60"
          let w__6 ← (( do readReg __DCACHE_CCSIDR_RESET ) : SailM (Vector (BitVec 64) 7) )
          (pure ((GetElem?.getElem! w__6 (Sail.Int.toNatChecked (level)))))))
  | 0b011 =>
    (do
      if (data_cache : Bool)
      then
        (do
          ArmFull.assert ((0 ≤b level) && (level <b 7)) "sail-inputs/12-sysregs.sail:234.59-234.60"
          let w__8 ← (( do readReg __DCACHE_CCSIDR_RESET ) : SailM (Vector (BitVec 64) 7) )
          (pure ((GetElem?.getElem! w__8 (Sail.Int.toNatChecked (level))))))
      else
        (do
          ArmFull.assert ((0 ≤b level) && (level <b 7)) "sail-inputs/12-sysregs.sail:237.59-237.60"
          let w__9 ← (( do readReg __ICACHE_CCSIDR_RESET ) : SailM (Vector (BitVec 64) 7) )
          (pure ((GetElem?.getElem! w__9 (Sail.Int.toNatChecked (level)))))))
  | 0b100 =>
    (do
      ArmFull.assert ((0 ≤b level) && (level <b 7)) "sail-inputs/12-sysregs.sail:242.55-242.56"
      let w__11 ← (( do readReg __DCACHE_CCSIDR_RESET ) : SailM (Vector (BitVec 64) 7) )
      let ccsidr_val := ((GetElem?.getElem! w__11 (Sail.Int.toNatChecked (level))) : (BitVec 64))
      (pure (ccsidr_val)))
  | _ => (pure (ccsidr_val))


def decode_aarch32_instrs_CLREX_A1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_CLREX_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_CLREX_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_CLREX_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_DBG_A1enc_A_txt (cond : (BitVec 4)) (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:2824.29-2824.30"
      (pure ((execute_aarch32_instrs_DBG_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_DBG_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_DBG_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_ISB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_ISB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_ISB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_ISB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_NOP_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:8241.29-8241.30"
      (pure ((execute_aarch32_instrs_NOP_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_NOP_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_NOP_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_NOP_T2enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_NOP_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_SB_A1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_SB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SEV_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:11377.29-11377.30"
      (pure ((execute_aarch32_instrs_SEV_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_SEV_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_SEV_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_SEV_T2enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_SEV_Op_A_txt ())
    else ()
  (pure (()))


def decode_aarch32_instrs_UDF_A1enc_A_txt (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm12 +++ imm4) 32)
      (execute_aarch32_instrs_UDF_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_UDF_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_UDF_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_UDF_T2enc_A_txt (imm4 : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4 +++ imm12) 32)
      (execute_aarch32_instrs_UDF_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_YIELD_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:40636.29-40636.30"
      (pure ((execute_aarch32_instrs_YIELD_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_YIELD_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__0 : Bool)
    then (execute_aarch32_instrs_YIELD_Op_A_txt ())
    else ()
  (pure (()))


end ArmFull.Functions
