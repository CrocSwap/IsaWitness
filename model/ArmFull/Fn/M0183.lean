module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182 set_option backward.proofsInPublic true @[expose] public section

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

def AArch32_WriteMode (mode : (BitVec 5)) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 643) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 644) ()) ) : SailM Bool )
  let w__0 ← (( do (ELFromM32 mode) ) : SailM (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let valid_name : Bool := tup__0
  let el : (BitVec 2) := tup__1
  ArmFull.assert valid_name "sail-inputs/03-v8_base.sail:8284.21-8284.22"
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with M := mode }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with EL := el }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with nRW := 1#1 }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with SP := if (((mode == M32_User) || (mode == M32_System)) : Bool)
    then 0#1
    else 1#1 }


def AArch32_GenerateDebugExceptionsFrom (from_el : (BitVec 2)) (from_state : SecurityState) : SailM Bool := do
  let mask ← (( do (undefined_bitvector_at (← occLabel 652) 1) ) : SailM (BitVec 1) )
  let spd ← (( do (undefined_bitvector_at (← occLabel 653) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (DebugTargetFrom from_state) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      let mask : (BitVec 1) := 0#1
      (AArch64_GenerateDebugExceptionsFrom from_el from_state mask))
  else
    (do
      let w__7 ← (( do
        if ((← do
             if ((← do
                  let w__3 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
                  (pure ((((_get_DBGOSLSR_Type_OSLK w__3) == 1#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 (DoubleLockStatus ()))) : Bool)
        then (pure true)
        else
          (do
            (Halted ())) ) : SailM Bool )
      if (w__7 : Bool)
      then (pure (false))
      else
        (do
          let enabled ← (( do (undefined_bool_at (← occLabel 654) ()) ) : SailM Bool )
          let w__9 ← (( do
            (pure ((← do
                  (HaveEL EL3)) && ((BEq.beq from_state SS_Secure) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              ArmFull.assert (from_el != EL2) "sail-inputs/03-v8_base.sail:8455.29-8455.30"
              let w__10 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
              let enabled ← (( do
                if (w__10 : Bool)
                then
                  (do
                    let w__11 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                    let enabled := (((_get_MDCR_EL3_Type_SDD w__11) == 0#1) : Bool)
                    (pure (enabled)))
                else
                  (do
                    let w__12 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                    let spd ← (( do
                      if (w__12 : Bool)
                      then
                        (do
                          let w__13 ← (( do readReg SDCR ) : SailM (BitVec 32) )
                          (pure ((_get_SDCR_Type_SPD w__13))))
                      else
                        (do
                          let w__14 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((_get_MDCR_EL3_Type_SPD32 w__14)))) ) : SailM (BitVec 2) )
                    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spd 1)])) == 1#1) : Bool)
                    then
                      (let enabled : Bool :=
                        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spd 0)])) == 1#1)
                      (pure (enabled)))
                    else
                      (do
                        (AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled ()))) ) : SailM Bool
                )
              if ((from_el == EL0) : Bool)
              then
                (do
                  if ((enabled : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__16 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
                      (pure ((((_get_SDER_Type_SUIDEN w__16) == 1#1) : Bool)))))
              else (pure (enabled)))
          else
            (let enabled : Bool := (from_el != EL2)
            (pure (enabled)))))


def AArch64_MaybeZeroRegisterUppers (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:8998.25-8998.26"
  let first : Int := 0
  let last : Int := 14
  let include_R15_name ← (( do (undefined_bool_at (← occLabel 670) ()) ) : SailM Bool )
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__1.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__2 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__2) : Bool))))
    else (pure false) ) : SailM Bool )
  let (first, include_R15_name, last) ← (( do
    if (w__3 : Bool)
    then
      (let first : Int := 0
      let last : Int := 14
      let include_R15_name : Bool := false
      (pure ((first, include_R15_name, last))))
    else
      (do
        let w__10 ← (( do
          if ((← do
               if ((← do
                    if ((← do
                         let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__4.EL == EL0) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__5.EL == EL1) : Bool))))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__9 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              (pure (((! w__9) : Bool))))
          else (pure false) ) : SailM Bool )
        let (first, include_R15_name, last) : (Int × Bool × Int) :=
          if (w__10 : Bool)
          then
            (let first : Int := 0
            let last : Int := 30
            let include_R15_name : Bool := false
            (first, include_R15_name, last))
          else
            (let first : Int := 0
            let last : Int := 30
            let include_R15_name : Bool := true
            (first, include_R15_name, last))
        (pure ((first, include_R15_name, last)))) ) : SailM (Int × Bool × Int) )
  let last : Int := last
  let first : Int := first
  let loop_n_lower : Int := first
  let loop_n_upper : Int := last
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__12 ← (( do
          if ((((n != 15) || include_R15_name) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_ZEROUPPER))
          else (pure false) ) : SailM Bool )
        if (w__12 : Bool)
        then
          (do
            (set_R_bits (Sail.Int.toNatChecked (n)) 63 32 (Zeros (n := 32))))
        else (pure (()))
    (pure loop_vars))


def InterruptPending (_ : Unit) : SailM Bool := do
  let fiq_pending ← (( do (undefined_bool_at (← occLabel 735) ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool_at (← occLabel 736) ()) ) : SailM Bool )
  let pending_virtual_interrupt : Bool := false
  let (__tup_0, _) ← (( do (IRQPending ()) ) : SailM (Bool × Bool) )
  let irq_pending : Bool := __tup_0
  let (__tup_0, _) := (FIQPending ())
  let fiq_pending : Bool := __tup_0
  let pending_physical_interrupt : Bool :=
    ((irq_pending || fiq_pending) || (IsPhysicalSErrorPending ()))
  let w__6 ← (( do
    if ((← do
         if ((← do
              (EL2Enabled ())) : Bool)
         then
           (do
             if ((← do
                  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__1.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__2.EL == EL1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let pending_virtual_interrupt ← (( do
    if (w__6 : Bool)
    then
      (do
        let virq_pending ← (( do
          if ((← do
               let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_HCR_EL2_Type_IMO w__7) == 1#1) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   (VirtualIRQPending ())) : Bool)
              then (pure true)
              else
                (do
                  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VI w__9) == 1#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let vfiq_pending ← (( do
          if ((← do
               let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_HCR_EL2_Type_FMO w__11) == 1#1) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   (VirtualFIQPending ())) : Bool)
              then (pure true)
              else
                (do
                  let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VF w__13) == 1#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let vsei_pending ← (( do
          if ((← do
               let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_HCR_EL2_Type_AMO w__15) == 1#1) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   (IsVirtualSErrorPending ())) : Bool)
              then (pure true)
              else
                (do
                  let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VSE w__17) == 1#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let pending_virtual_interrupt : Bool := ((vsei_pending || virq_pending) || vfiq_pending)
        (pure (pending_virtual_interrupt)))
    else (pure (pending_virtual_interrupt)) ) : SailM Bool )
  (pure ((pending_physical_interrupt || pending_virtual_interrupt)))


def IsHCRXEL2Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatHCX ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_HXEn w__2) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (false))
      else
        (do
          (EL2Enabled ())))


def UsePrimarySpaceEL10 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  if (((_get_MPAM3_EL3_Type_ALTSP_HEN w__0) == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_MPAM3_EL3_Type_ALTSP_HFC w__1) == 0#1))))
  else
    (do
      if ((← do
           if ((← do
                let w__2 ← (( do (MPAMisEnabled ()) ) : SailM Bool )
                (pure (((! w__2) : Bool)))) : Bool)
           then (pure true)
           else
             (do
               let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
               (pure (((! w__3) : Bool))))) : Bool)
      then (pure true)
      else
        (do
          let w__5 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_MPAM2_EL2_Type_ALTSP_HFC w__5) == 0#1) : Bool)))))


def MPAMisVirtual (el : (BitVec 2)) : SailM Bool := do
  if ((← do
       if ((← do
            let w__0 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_MPAMIDR_EL1_Type_HAS_HCR w__0) == 1#1) : Bool)))) : Bool)
       then
         (do
           (EL2Enabled ()))
       else (pure false)) : Bool)
  then
    (do
      if ((← do
           if ((← do
                if (((el == EL0) : Bool) : Bool)
                then
                  (do
                    let w__3 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_MPAMHCR_EL2_Type_EL0_VPMEN w__3) == 1#1) : Bool))))
                else (pure false)) : Bool)
           then
             (do
               if ((← do
                    let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_E2H w__5) == 0#1) : Bool)))) : Bool)
               then (pure true)
               else
                 (do
                   let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__6) == 0#1) : Bool)))))
           else (pure false)) : Bool)
      then (pure true)
      else
        (do
          if (((el == EL1) : Bool) : Bool)
          then
            (do
              let w__9 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_MPAMHCR_EL2_Type_EL1_VPMEN w__9) == 1#1) : Bool))))
          else (pure false)))
  else (pure false)


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool -/
def getMPAM_PARTID (MPAMn : (BitVec 2)) (InD : Bool) (InSM : Bool) : SailM (BitVec 16) := do
  let partid ← (( do (undefined_bitvector_at (← occLabel 763) 16) ) : SailM PARTIDtype )
  let el2avail ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (InSM : Bool)
  then
    (do
      let w__0 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
      let partid := ((_get_MPAMSM_EL1_Type_PARTID_D w__0) : (BitVec 16))
      (pure (partid)))
  else
    (do
      if (InD : Bool)
      then
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM3_EL3_Type_PARTID_I w__1) : (BitVec 16))
              (pure (partid)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PARTID_I w__2))))
              else (pure ((Zeros (n := 16)))))
          | 0b01 =>
            (do
              let w__4 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM1_EL1_Type_PARTID_I w__4) : (BitVec 16))
              (pure (partid)))
          | 0b00 =>
            (do
              let w__5 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM0_EL1_Type_PARTID_I w__5) : (BitVec 16))
              (pure (partid)))
          | _ =>
            (do
              (__UNKNOWN_PARTIDtype ())))
      else
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__7 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM3_EL3_Type_PARTID_D w__7) : (BitVec 16))
              (pure (partid)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__8 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PARTID_D w__8))))
              else (pure ((Zeros (n := 16)))))
          | 0b01 =>
            (do
              let w__10 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM1_EL1_Type_PARTID_D w__10) : (BitVec 16))
              (pure (partid)))
          | 0b00 =>
            (do
              let w__11 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM0_EL1_Type_PARTID_D w__11) : (BitVec 16))
              (pure (partid)))
          | _ =>
            (do
              (__UNKNOWN_PARTIDtype ()))))


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool -/
def getMPAM_PMG (MPAMn : (BitVec 2)) (InD : Bool) (InSM : Bool) : SailM (BitVec 8) := do
  let pmg ← (( do (undefined_bitvector_at (← occLabel 764) 8) ) : SailM PMGtype )
  let el2avail ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (InSM : Bool)
  then
    (do
      let w__0 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
      let pmg := ((_get_MPAMSM_EL1_Type_PMG_D w__0) : (BitVec 8))
      (pure (pmg)))
  else
    (do
      if (InD : Bool)
      then
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM3_EL3_Type_PMG_I w__1) : (BitVec 8))
              (pure (pmg)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PMG_I w__2))))
              else (pure ((Zeros (n := 8)))))
          | 0b01 =>
            (do
              let w__4 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM1_EL1_Type_PMG_I w__4) : (BitVec 8))
              (pure (pmg)))
          | 0b00 =>
            (do
              let w__5 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM0_EL1_Type_PMG_I w__5) : (BitVec 8))
              (pure (pmg)))
          | _ =>
            (do
              (__UNKNOWN_PMGtype ())))
      else
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__7 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM3_EL3_Type_PMG_D w__7) : (BitVec 8))
              (pure (pmg)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__8 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PMG_D w__8))))
              else (pure ((Zeros (n := 8)))))
          | 0b01 =>
            (do
              let w__10 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM1_EL1_Type_PMG_D w__10) : (BitVec 8))
              (pure (pmg)))
          | 0b00 =>
            (do
              let w__11 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM0_EL1_Type_PMG_D w__11) : (BitVec 8))
              (pure (pmg)))
          | _ =>
            (do
              (__UNKNOWN_PMGtype ()))))


def ExtAbortToA64 (fault : FaultRecord) : SailM Bool := do
  let route_to_aarch64 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__5 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__5 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if ((← do
                       let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      (IsSecondStage fault))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      if ((← do
                           (HaveRASExt ())) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_TEA w__10) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (IsExternalAbort__1 fault))
                 else (pure false))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (IsDebugException fault)) : Bool)
            then
              (do
                let w__16 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_TDE w__16) == 1#1) : Bool))))
            else (pure false)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__22 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (HaveEL EL3))
         else (pure false)) : Bool)
    then
      (do
        let w__21 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__21) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__22 : Bool)
    then
      (do
        if ((← do
             let w__23 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
             (pure ((((_get_SCRType_EA w__23) == 1#1) : Bool)))) : Bool)
        then
          (do
            (IsExternalAbort__1 fault))
        else (pure false))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if ((route_to_aarch64 : Bool) : Bool)
  then
    (do
      (IsExternalSyncAbort fault.statuscode))
  else (pure false)


def IsSCTLR2EL2Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatSCTLR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_SCTLR2En w__2) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (false))
      else
        (do
          (EL2Enabled ())))


end ArmFull.Functions
