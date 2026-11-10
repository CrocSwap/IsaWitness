import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0108
import ArmFull.Fn.M0119
import ArmFull.Fn.M0144
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0156
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0188
import ArmFull.Fn.M0195
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0217
import ArmFull.Fn.M0218

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

/-- Type quantifiers: k_N : Nat, 31 < k_N -/
def SetPSTATEFromPSR (spsr : (BitVec k_N)) : SailM Unit := do
  let illegal_psr_state ← (( do (IllegalExceptionReturn spsr) ) : SailM Bool )
  (SetPSTATEFromPSR__1 spsr illegal_psr_state)


def MaybeZeroSVEUppers (target_el : (BitVec 2)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let lower_enabled ← (( do (undefined_bool_at (← occLabel 682) ()) ) : SailM Bool )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure ((((BitVec.toNat target_el) ≤b (BitVec.toNat w__0.EL)) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (IsSVEEnabled target_el) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (()))
  else
    (do
      let lower_enabled ← (( do
        if ((target_el == EL3) : Bool)
        then
          (do
            let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
            if (w__3 : Bool)
            then
              (do
                (IsFPEnabled EL2))
            else
              (do
                (IsFPEnabled EL1)))
        else
          (do
            if ((target_el == EL2) : Bool)
            then
              (do
                let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                ArmFull.assert (! w__6) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:9451.44-9451.45"
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                if (((_get_HCR_EL2_Type_TGE w__7) == 0#1) : Bool)
                then
                  (do
                    (IsFPEnabled EL1))
                else
                  (do
                    (IsFPEnabled EL0)))
            else
              (do
                let w__11 ← (( do
                  if (((target_el == EL1) : Bool) : Bool)
                  then
                    (do
                      let w__10 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__10) : Bool))))
                  else (pure false) ) : SailM Bool )
                ArmFull.assert w__11 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:9458.63-9458.64"
                (IsFPEnabled EL0))) ) : SailM Bool )
      if (lower_enabled : Bool)
      then
        (do
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__14 ← (( do (IsSVEEnabled w__13.EL) ) : SailM Bool )
          let VL : Int :=
            if (w__14 : Bool)
            then VL
            else 128
          let PL : Int := (Int.ediv (Sail.Int.toNatChecked (VL)) 8)
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 31
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__15 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) :
                  SailM Bool )
                if (w__15 : Bool)
                then
                  (do
                    let w__16 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
                    let w__17 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
                    writeReg _Z (vectorUpdate w__16 (Sail.Int.toNatChecked (n))
                      (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.zeroExtend
                        (Sail.BitVec.extractLsb
                          (GetElem?.getElem! w__17 (Sail.Int.toNatChecked (n)))
                          (Sail.Int.toNatChecked ((VL -i 1))) 0) MAX_VL))))
                else (pure (()))
            (pure loop_vars))
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 15
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__18 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) :
                  SailM Bool )
                if (w__18 : Bool)
                then
                  (do
                    let w__19 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
                    let w__20 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
                    writeReg _P (vectorUpdate w__19 (Sail.Int.toNatChecked (n))
                      (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.zeroExtend
                        (Sail.BitVec.extractLsb
                          (GetElem?.getElem! w__20 (Sail.Int.toNatChecked (n)))
                          (Sail.Int.toNatChecked ((PL -i 1))) 0) MAX_PL))))
                else (pure (()))
            (pure loop_vars))
          let w__21 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) : SailM Bool
            )
          if (w__21 : Bool)
          then
            (do
              let w__22 ← (( do readReg _FFR ) : SailM (BitVec 256) )
              writeReg _FFR (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.zeroExtend
                (Sail.BitVec.extractLsb w__22 (Sail.Int.toNatChecked ((PL -i 1))) 0) MAX_PL)))
          else (pure (()))
          let w__25 ← (( do
            if ((← do
                 (HaveSME ())) : Bool)
            then
              (do
                let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__24.ZA == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__25 : Bool)
          then
            (do
              let SVL : Int := SVL
              let accessiblevecs : Int := (Int.ediv (Sail.Int.toNatChecked (SVL)) 8)
              let w__26 ← (( do (MaxImplementedSVL ()) ) : SailM Int )
              let allvecs : Int := (fdiv_int w__26 8)
              let loop_n_lower : Nat := 0
              let loop_n_upper : Int := (accessiblevecs -i 1)
              (do
                let mut loop_vars := ()
                for n in [loop_n_lower:loop_n_upper:1]i do
                  let () := loop_vars
                  loop_vars ← do
                    let w__27 ← (( do (ConstrainUnpredictableBool Unpredictable_SMEZEROUPPER) ) :
                      SailM Bool )
                    if (w__27 : Bool)
                    then
                      (do
                        let w__28 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
                        let w__29 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
                        writeReg _ZA (vectorUpdate w__28 (Sail.Int.toNatChecked (n))
                          (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.zeroExtend
                            (Sail.BitVec.extractLsb
                              (GetElem?.getElem! w__29 (Sail.Int.toNatChecked (n)))
                              (Sail.Int.toNatChecked ((SVL -i 1))) 0) MAX_VL))))
                    else (pure (()))
                (pure loop_vars))
              let loop_n_lower : Int := accessiblevecs
              let loop_n_upper : Int := (allvecs -i 1)
              (do
                let mut loop_vars := ()
                for n in [loop_n_lower:loop_n_upper:1]i do
                  let () := loop_vars
                  loop_vars ← do
                    let w__30 ← (( do (ConstrainUnpredictableBool Unpredictable_SMEZEROUPPER) ) :
                      SailM Bool )
                    if (w__30 : Bool)
                    then
                      (do
                        ArmFull.assert ((0 ≤b n) && (n <b 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:9491.69-9491.70"
                        let w__31 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
                        writeReg _ZA (vectorUpdate w__31 (Sail.Int.toNatChecked (n))
                          (Sail.BitVec.castWidth (m := 2048) (Zeros (n := MAX_VL)))))
                    else (pure (()))
                (pure loop_vars)))
          else (pure (())))
      else (pure (())))


def AArch32_PendingUnmaskedPhysicalInterrupts (_ : Unit) : SailM (Bool × Bool × Bool) := do
  let fiq ← (( do (undefined_bool_at (← occLabel 713) ()) ) : SailM Bool )
  let irq ← (( do (undefined_bool_at (← occLabel 714) ()) ) : SailM Bool )
  let mask_override ← (( do (undefined_bitvector_at (← occLabel 715) 3) ) : SailM (BitVec 3) )
  let w__1 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_PendingUnmaskedPhysicalInterrupts (w__2.A +++ (w__3.I +++ w__4.F))))
  else
    (do
      let se_pending : (BitVec 1) :=
        if ((IsPhysicalSErrorPending ()) : Bool)
        then 1#1
        else 0#1
      let (__tup_0, _) ← (( do (IRQPending ()) ) : SailM (Bool × Bool) )
      let irq : Bool := __tup_0
      let (__tup_0, _) := (FIQPending ())
      let fiq : Bool := __tup_0
      let irq_pending : (BitVec 1) :=
        if (irq : Bool)
        then 1#1
        else 0#1
      let fiq_pending : (BitVec 1) :=
        if (fiq : Bool)
        then 1#1
        else 0#1
      let pending : (BitVec 3) := ((se_pending +++ irq_pending) +++ fiq_pending)
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      let mask : (BitVec 3) := (w__6.A +++ (w__7.I +++ w__8.F))
      let w__13 ← (( do
        if ((← do
             if ((← do
                  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__9.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__10.EL == EL1) : Bool))))) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailM Bool )
      let mask ← (( do
        if (w__13 : Bool)
        then
          (do
            let w__14 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let mask_override ← (( do
              if (((_get_HCR_Type_TGE w__14) == 1#1) : Bool)
              then (pure (0b111#3))
              else
                (do
                  let w__15 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                  let w__16 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                  let w__17 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                  (pure (((_get_HCR_Type_AMO w__15) +++ ((_get_HCR_Type_IMO w__16) +++ (_get_HCR_Type_FMO
                          w__17)))))) ) : SailM (BitVec 3) )
            let mask : (BitVec 3) := (mask &&& (Complement.complement mask_override))
            (pure (mask)))
        else (pure (mask)) ) : SailM (BitVec 3) )
      let w__19 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__18 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne w__18 SS_Secure) : Bool))))
        else (pure false) ) : SailM Bool )
      let mask ← (( do
        if (w__19 : Bool)
        then
          (do
            let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
            if ((w__20.EL != EL3) : Bool)
            then
              (do
                let w__25 ← (( do
                  if ((← do
                       let w__21 ← (( do readReg SCR ) : SailM (BitVec 32) )
                       (pure ((((_get_SCR_Type_FIQ w__21) == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      if ((← do
                           let w__22 ← (( do readReg SCR ) : SailM (BitVec 32) )
                           (pure ((((_get_SCR_Type_FW w__22) == 0#1) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__23 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_HCR_Type_FMO w__23) == 1#1) : Bool)))))
                  else (pure false) ) : SailM Bool )
                let mask : (BitVec 3) :=
                  if (w__25 : Bool)
                  then (BitVec.update mask 0 (Bit 0#1))
                  else mask
                let w__28 ← (( do
                  if ((← do
                       let w__26 ← (( do readReg SCR ) : SailM (BitVec 32) )
                       (pure ((((_get_SCR_Type_IRQ w__26) == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      let w__27 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((((_get_HCR_Type_IMO w__27) == 1#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let mask : (BitVec 3) :=
                  if (w__28 : Bool)
                  then (BitVec.update mask 1 (Bit 0#1))
                  else mask
                let w__33 ← (( do
                  if ((← do
                       let w__29 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
                       (pure (((w__29 == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      if ((← do
                           let w__30 ← (( do readReg SCR ) : SailM (BitVec 32) )
                           (pure ((((_get_SCR_Type_AW w__30) == 0#1) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__31 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_HCR_Type_AMO w__31) == 1#1) : Bool)))))
                  else (pure false) ) : SailM Bool )
                let mask : (BitVec 3) :=
                  if (w__33 : Bool)
                  then (BitVec.update mask 2 (Bit 0#1))
                  else mask
                (pure (mask)))
            else (pure (mask)))
        else (pure (mask)) ) : SailM (BitVec 3) )
      let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access unmasked_pending 2)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              unmasked_pending 1)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              unmasked_pending 0)])) == 1#1)))))


def NewAccDesc (acctype : AccessType) : SailM AccessDescriptor := do
  let accdesc ← (( do (undefined_AccessDescriptor (← occLabel 769) ()) ) : SailM
    AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acctype := acctype }
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc := ({ accdesc with el := w__0.EL } : AccessDescriptor)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (SecurityStateAtEL w__1.EL) ) : SailM SecurityState )
  let accdesc := ({ accdesc with ss := w__2 } : AccessDescriptor)
  let accdesc : AccessDescriptor := { accdesc with acqsc := false }
  let accdesc : AccessDescriptor := { accdesc with acqpc := false }
  let accdesc : AccessDescriptor := { accdesc with relsc := false }
  let accdesc : AccessDescriptor := { accdesc with limitedordered := false }
  let accdesc : AccessDescriptor := { accdesc with exclusive := false }
  let accdesc : AccessDescriptor := { accdesc with rcw := false }
  let accdesc : AccessDescriptor := { accdesc with rcws := false }
  let accdesc : AccessDescriptor := { accdesc with atomicop := false }
  let accdesc : AccessDescriptor := { accdesc with nontemporal := false }
  let accdesc : AccessDescriptor := { accdesc with read := false }
  let accdesc : AccessDescriptor := { accdesc with write := false }
  let accdesc : AccessDescriptor := { accdesc with pan := false }
  let accdesc : AccessDescriptor := { accdesc with nonfault := false }
  let accdesc : AccessDescriptor := { accdesc with firstfault := false }
  let accdesc : AccessDescriptor := { accdesc with first := false }
  let accdesc : AccessDescriptor := { accdesc with contiguous := false }
  let accdesc : AccessDescriptor := { accdesc with streamingsve := false }
  let accdesc : AccessDescriptor := { accdesc with ls64 := false }
  let accdesc : AccessDescriptor := { accdesc with mops := false }
  let accdesc : AccessDescriptor := { accdesc with a32lsmd := false }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := false }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := false }
  let accdesc : AccessDescriptor := { accdesc with transactional := false }
  let w__3 ← (( do (GenMPAMcurEL acctype) ) : SailM MPAMinfo )
  let accdesc := ({ accdesc with mpam := w__3 } : AccessDescriptor)
  (pure (accdesc))


def AArch64_GetS1TTWParams (regime : Regime) (ss : SecurityState) (va : (BitVec 64)) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1274) ()) ) : SailM S1TTWParams )
  let varange : VARange := (AArch64_GetVARange va)
  match regime with
  | .Regime_EL3 =>
    (do
      (AArch64_S1TTWParamsEL3 ()))
  | .Regime_EL2 =>
    (do
      (AArch64_S1TTWParamsEL2 ss))
  | .Regime_EL20 =>
    (do
      (AArch64_S1TTWParamsEL20 ss varange))
  | .Regime_EL10 =>
    (do
      (AArch64_S1TTWParamsEL10 varange))
  | _ => (pure (walkparams))


/-- Type quantifiers: n : Int, part : Int, width : Nat, width ≥ 0 -/
def Vpart_set (n : Int) (part : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22361.27-22361.28"
  ArmFull.assert ((part == 0) || (part == 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22362.32-22362.33"
  if ((part == 0) : Bool)
  then
    (do
      ArmFull.assert (width <b 128) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22364.26-22364.27"
      ArmFull.assert (((((width == 8) || (width == 16)) || (width == 32)) || (width == 64)) || (width == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22365.57-22365.58"
      (V_set n width (Sail.BitVec.castWidth value_name)))
  else
    (do
      ArmFull.assert (width == 64) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:22368.26-22368.27"
      let vreg ← (( do (V_read n 64) ) : SailM (BitVec 64) )
      (V_set n 128 ((Sail.BitVec.extractLsb value_name 63 0) +++ vreg)))


def AArch64_ResetSIMDFPRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 31
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
        (V_set i 128 w__0)
    (pure loop_vars))


/-- Type quantifiers: k_ex10456192_ : Bool, k_ex10456191_ : Bool -/
def C27bConstrainBP (aarch64 : Bool) (context_aware : Bool) : SailM (Constraint × (BitVec 5)) := do
  let disabled ← (( do (undefined_bool_at (← occLabel 1363) ()) ) : SailM Bool )
  if (disabled : Bool)
  then
    (do
      let w__0 ← (( do (undefined_bitvector_at (← occLabel 1364) 5) ) : SailM (BitVec 5) )
      (pure ((Constraint_DISABLED, (w__0 : (BitVec 5))))))
  else
    (do
      let allowed : (BitVec 256) := (Zeros (n := 256))
      let allowed ← (( do
        let loop_i_lower : Nat := 0
        let loop_i_upper : Nat := 31
        (do
          let mut loop_vars := allowed
          for i in [loop_i_lower:loop_i_upper:1]i do
            let allowed := loop_vars
            loop_vars ← do
              let raw : (BitVec 5) := (integer_subrange i 4 0)
              let valid ← (( do
                if (aarch64 : Bool)
                then
                  (do
                    let w__1 ← (( do
                      (C27bReservedBP64 (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access raw 4)]))
                        (Sail.BitVec.extractLsb raw 3 0) context_aware) ) : SailM Bool )
                    (pure ((! w__1))))
                else
                  (do
                    if (((i <b 16) : Bool) : Bool)
                    then
                      (do
                        let w__2 ← (( do
                          (C27bReservedBP32 (Sail.BitVec.extractLsb raw 3 0) context_aware) ) :
                          SailM Bool )
                        (pure (((! w__2) : Bool))))
                    else (pure false)) ) : SailM Bool )
              let allowed : (BitVec 256) :=
                if (valid : Bool)
                then (BitVec.update allowed (Sail.Int.toNatChecked (i)) 1#1)
                else allowed
              (pure (allowed))
          (pure loop_vars)) ) : SailM (BitVec 256) )
      let selected ← (( do (C27bSelect allowed) ) : SailM Int )
      (pure ((Constraint_UNKNOWN, (integer_subrange selected 4 0)))))


def AArch64_GetS1TLBContext (regime : Regime) (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1476) ()) ) : SailM TLBContext )
  let tlbcontext ← (( do
    match regime with
    | .Regime_EL3 =>
      (do
        (AArch64_TLBContextEL3 ss va tg))
    | .Regime_EL2 =>
      (do
        (AArch64_TLBContextEL2 ss va tg))
    | .Regime_EL20 =>
      (do
        (AArch64_TLBContextEL20 ss va tg))
    | .Regime_EL10 =>
      (do
        (AArch64_TLBContextEL10 ss va tg))
    | _ => (pure (tlbcontext)) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with includes_s1_name := true }
  let tlbcontext : TLBContext := { tlbcontext with includes_s2_name := false }
  let tlbcontext : TLBContext := { tlbcontext with includes_gpt_name := false }
  (pure (tlbcontext))


def AArch64_S1InitialTTWState (walkparams : S1TTWParams) (va : (BitVec 64)) (regime : Regime) (ss : SecurityState) : SailM TTWState := do
  let walkstate ← (( do (undefined_TTWState (← occLabel 1481) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1482) ()) ) : SailM FullAddress )
  let permissions ← (( do (undefined_Permissions (← occLabel 1483) ()) ) : SailM Permissions )
  let ttbr ← (( do (AArch64_S1TTBR regime va) ) : SailM (BitVec 128) )
  let tablebase : FullAddress :=
    match ss with
    | .SS_Secure => { tablebase with paspace := PAS_Secure }
    | .SS_NonSecure => { tablebase with paspace := PAS_NonSecure }
    | .SS_Root => { tablebase with paspace := PAS_Root }
    | .SS_Realm => { tablebase with paspace := PAS_Realm }
  let w__0 ← (( do (AArch64_S1TTBaseAddress walkparams regime ttbr) ) : SailM (BitVec 56) )
  let tablebase := ({ tablebase with address := w__0 } : FullAddress)
  let permissions : Permissions := { permissions with ap_table := 0b00#2 }
  let permissions : Permissions :=
    if ((HasUnprivileged regime) : Bool)
    then
      (let permissions : Permissions := { permissions with uxn_table := 0#1 }
      { permissions with pxn_table := 0#1 })
    else { permissions with xn_table := 0#1 }
  let walkstate : TTWState := { walkstate with baseaddress := tablebase }
  let walkstate : TTWState := { walkstate with level := (AArch64_S1StartLevel walkparams) }
  let walkstate : TTWState := { walkstate with istable := true }
  let walkstate : TTWState :=
    { walkstate with nG := if ((HasUnprivileged regime) : Bool)
      then 1#1
      else 0#1 }
  let w__1 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) : SailM
    MemoryAttributes )
  let walkstate := ({ walkstate with memattrs := w__1 } : TTWState)
  let walkstate : TTWState := { walkstate with permissions := permissions }
  let walkstate : TTWState :=
    if (((walkparams.d128 == 1#1) || (walkparams.pnch == 1#1)) : Bool)
    then { walkstate with s1assured := true }
    else { walkstate with s1assured := false }
  let walkstate : TTWState := { walkstate with disch := walkparams.disch }
  (pure (walkstate))


/-- Type quantifiers: esize : Nat, slice_name : Int, tile : Int, width : Nat, width ≥ 0 ∧
  esize ≥ 0 ∧
  (Sail.Int.toNatChecked ((slice_name : Int) *i (esize : Int))) ≤
  (Sail.Int.toNatChecked ((((slice_name : Int) *i (esize : Int)) +i (esize : Int)) -i (1 : Int)))
  ∨
  (not
  ((Sail.Int.toNatChecked (slice_name : Int)) ≥ 0 ∧
  (Sail.Int.toNatChecked (((slice_name : Int) +i (1 : Int)) *i (esize : Int))) ≤ width)) -/
def ZAvslice_read (tile : Int) (esize : Nat) (slice_name : Int) (width : Nat) : SailM (BitVec width) := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let slices : Int := (fdiv_int SVL esize)
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1751)
      (Sail.Int.toNatChecked (width)))) ) : SailM (BitVec width) )
  let loop_s_lower : Nat := 0
  let loop_s_upper : Int := (slices -i 1)
  (do
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let hslice ← (( do ((Sail.BitVec.castWidth ) <$> (ZAhslice_read tile esize s width)) ) :
          SailM (BitVec width) )
        ArmFull.assert (((s *i esize) ≤b (((s +i 1) *i esize) -i 1)) || (! ((s ≥b 0) && (((s +i 1) *i esize) ≤b width)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:31191.132-31191.133"
        let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read hslice slice_name esize)) ) :
          SailM (BitVec esize) )
        (Elem_set result s esize (Sail.BitVec.castWidth w__0))
    (pure loop_vars))


/-- Type quantifiers: esize : Nat, slice_name : Int, tile : Int, width : Nat, width ≥ 0 ∧
  esize ≥ 0 -/
def ZAvslice_set (tile : Int) (esize : Nat) (slice_name : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let slices : Int := (fdiv_int SVL esize)
  let loop_s_lower : Nat := 0
  let loop_s_upper : Int := (slices -i 1)
  (do
    let mut loop_vars := ()
    for s in [loop_s_lower:loop_s_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let hslice ← (( do ((Sail.BitVec.castWidth ) <$> (ZAhslice_read tile esize s width)) ) :
          SailM (BitVec width) )
        ArmFull.assert (((s *i esize) ≤b (((s *i esize) +i esize) -i 1)) || (! ((s ≥b 0) && (((s +i 1) *i esize) ≤b width)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:31206.135-31206.136"
        let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read value_name s esize)) ) : SailM
          (BitVec esize) )
        let w__1 ← (( do (Elem_set hslice slice_name esize (Sail.BitVec.castWidth w__0)) ) : SailM
          (BitVec width) )
        let hslice := (w__1 : (BitVec width))
        (ZAhslice_set tile esize s width (Sail.BitVec.castWidth hslice))
    (pure loop_vars))


/-- Type quantifiers: SVL : Int, esize : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAtile_read (SVL : Int) (tile : Int) (esize : Int) (width : Nat) : SailM (BitVec width) := do
  let slices : Int := (fdiv_int SVL esize)
  ArmFull.assert (width == (SVL *i slices)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:31249.32-31249.33"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1753)
      (Sail.Int.toNatChecked (width)))) ) : SailM (BitVec width) )
  let loop_slice_name_lower : Nat := 0
  let loop_slice_name_upper : Int := (slices -i 1)
  (do
    let mut loop_vars := result
    for slice_name in [loop_slice_name_lower:loop_slice_name_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        ArmFull.assert (((slice_name *i SVL) ≤b (((slice_name +i 1) *i SVL) -i 1)) || (! ((slice_name ≥b 0) && (((slice_name +i 1) *i SVL) ≤b width)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:31252.162-31252.163"
        let w__0 ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAhslice_read tile esize slice_name
            (Sail.Int.toNatChecked (SVL)))) ) : SailM (BitVec (Sail.Int.toNatChecked (SVL : Int))) )
        (Elem_set result slice_name (Sail.Int.toNatChecked (SVL)) (Sail.BitVec.castWidth w__0))
    (pure loop_vars))


/-- Type quantifiers: SVL : Int, esize : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAtile_set (SVL : Int) (tile : Int) (esize : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let slices : Int := (fdiv_int SVL esize)
  ArmFull.assert (width == (SVL *i slices)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:31264.32-31264.33"
  let loop_slice_name_lower : Nat := 0
  let loop_slice_name_upper : Int := (slices -i 1)
  (do
    let mut loop_vars := ()
    for slice_name in [loop_slice_name_lower:loop_slice_name_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        ArmFull.assert (((slice_name *i SVL) ≤b (((slice_name *i SVL) +i SVL) -i 1)) || (! ((slice_name ≥b 0) && (((slice_name +i 1) *i SVL) ≤b width)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:31266.163-31266.164"
        let w__0 ← (( do
          ((Sail.BitVec.castWidth ) <$> (Elem_read value_name slice_name
            (Sail.Int.toNatChecked (SVL)))) ) : SailM (BitVec (Sail.Int.toNatChecked (SVL : Int))) )
        (ZAhslice_set tile esize slice_name (Sail.Int.toNatChecked (SVL))
          (Sail.BitVec.castWidth w__0))
    (pure loop_vars))


end ArmFull.Functions
