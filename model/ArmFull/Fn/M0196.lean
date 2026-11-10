import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0014
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0113
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0152
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187

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

def UpdateEDSCRFields (_ : Unit) : SailM Unit := do
  let ss ← (( do (undefined_SecurityState (← occLabel 622) ()) ) : SailM SecurityState )
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_EL w__1 0b00#2))
      let w__2 ← (( do (HaveRME ()) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          let w__4 ← (( do (ExternalRootInvasiveDebugEnabled ()) ) : SailM Bool )
          let w__5 : (BitVec 1) :=
            if (w__4 : Bool)
            then 0#1
            else 1#1
          (EDSCR_write (_update_EDSCR_Type_SDD w__3 w__5))
          let __tmp ← (( do (EDSCR_read ()) ) : SailM EDSCR_Type )
          let split_vec ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
          let __tmp : EDSCR_Type :=
            (Sail.BitVec.updateSubrange __tmp 15 15 (Sail.BitVec.extractLsb split_vec 1 1))
          let __tmp : EDSCR_Type :=
            (Sail.BitVec.updateSubrange __tmp 18 18 (Sail.BitVec.extractLsb split_vec 0 0))
          (EDSCR_write __tmp))
      else
        (do
          let w__6 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          let w__7 ← (( do (ExternalSecureInvasiveDebugEnabled ()) ) : SailM Bool )
          let w__8 : (BitVec 1) :=
            if (w__7 : Bool)
            then 0#1
            else 1#1
          (EDSCR_write (_update_EDSCR_Type_SDD w__6 w__8))
          let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          let w__10 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
          (EDSCR_write (_update_EDSCR_Type_NS w__9 w__10)))
      let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_RW w__11 0b1111#4)))
  else
    (do
      let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      (EDSCR_write (_update_EDSCR_Type_EL w__12 w__13.EL))
      let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      let w__14 ← (( do (HaveRME ()) ) : SailM Bool )
      if (w__14 : Bool)
      then
        (do
          match ss with
          | .SS_Secure =>
            (do
              let __tmp ← (( do (EDSCR_read ()) ) : SailM EDSCR_Type )
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 15 15 (Sail.BitVec.extractLsb 0b00#2 1 1))
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 18 18 (Sail.BitVec.extractLsb 0b00#2 0 0))
              (EDSCR_write __tmp))
          | .SS_NonSecure =>
            (do
              let __tmp ← (( do (EDSCR_read ()) ) : SailM EDSCR_Type )
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 15 15 (Sail.BitVec.extractLsb 0b01#2 1 1))
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 18 18 (Sail.BitVec.extractLsb 0b01#2 0 0))
              (EDSCR_write __tmp))
          | .SS_Root =>
            (do
              let __tmp ← (( do (EDSCR_read ()) ) : SailM EDSCR_Type )
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 15 15 (Sail.BitVec.extractLsb 0b10#2 1 1))
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 18 18 (Sail.BitVec.extractLsb 0b10#2 0 0))
              (EDSCR_write __tmp))
          | .SS_Realm =>
            (do
              let __tmp ← (( do (EDSCR_read ()) ) : SailM EDSCR_Type )
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 15 15 (Sail.BitVec.extractLsb 0b11#2 1 1))
              let __tmp : EDSCR_Type :=
                (Sail.BitVec.updateSubrange __tmp 18 18 (Sail.BitVec.extractLsb 0b11#2 0 0))
              (EDSCR_write __tmp)))
      else
        (do
          let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          (EDSCR_write
            (_update_EDSCR_Type_NS w__15
              (if ((BEq.beq ss SS_Secure) : Bool)
              then 0#1
              else 1#1))))
      let RW ← (( do (undefined_bitvector_at (← occLabel 623) 4) ) : SailM (BitVec 4) )
      let w__16 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
      let w__17 : (BitVec 1) :=
        if (w__16 : Bool)
        then 0#1
        else 1#1
      let RW := ((BitVec.update RW 1 (Bit w__17)) : (BitVec 4))
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      let RW ← (( do
        if ((w__18.EL != EL0) : Bool)
        then
          (let RW : (BitVec 4) :=
            (BitVec.update RW 0 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 1)]))))
          (pure (RW)))
        else
          (do
            let w__19 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            let w__20 : (BitVec 1) :=
              if (w__19 : Bool)
              then 0#1
              else 1#1
            let RW := ((BitVec.update RW 0 (Bit w__20)) : (BitVec 4))
            (pure (RW))) ) : SailM (BitVec 4) )
      let w__25 ← (( do
        if (((! (HaveEL EL2)) : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if (((HaveEL EL3) : Bool) : Bool)
                 then
                   (do
                     let w__21 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
                     (pure ((((_get_SCRType_NS w__21) == 0#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__23 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
                (pure (((! w__23) : Bool))))
            else (pure false)) ) : SailM Bool )
      let RW ← (( do
        if (w__25 : Bool)
        then
          (let RW : (BitVec 4) :=
            (BitVec.update RW 2 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 1)]))))
          (pure (RW)))
        else
          (do
            let w__26 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
            let w__27 : (BitVec 1) :=
              if (w__26 : Bool)
              then 0#1
              else 1#1
            let RW := ((BitVec.update RW 2 (Bit w__27)) : (BitVec 4))
            (pure (RW))) ) : SailM (BitVec 4) )
      let RW ← (( do
        if ((! (HaveEL EL3)) : Bool)
        then
          (let RW : (BitVec 4) :=
            (BitVec.update RW 3 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 2)]))))
          (pure (RW)))
        else
          (do
            let w__28 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            let w__29 : (BitVec 1) :=
              if (w__28 : Bool)
              then 0#1
              else 1#1
            let RW := ((BitVec.update RW 3 (Bit w__29)) : (BitVec 4))
            (pure (RW))) ) : SailM (BitVec 4) )
      let RW ← (( do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 3)])) == 0#1) : Bool)
        then
          (do
            let w__30 ← (( do (__UNKNOWN_bits 3) ) : SailM (BitVec 3) )
            let RW := ((Sail.BitVec.updateSubrange RW 2 0 w__30) : (BitVec 4))
            (pure (RW)))
        else
          (do
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 2)])) == 0#1) : Bool)
            then
              (do
                let w__31 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
                let RW := ((Sail.BitVec.updateSubrange RW 1 0 w__31) : (BitVec 4))
                (pure (RW)))
            else
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 1)])) == 0#1) : Bool)
                then
                  (do
                    let w__32 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                    let RW := ((BitVec.update RW 0 (Bit w__32)) : (BitVec 4))
                    (pure (RW)))
                else (pure (RW)))) ) : SailM (BitVec 4) )
      let w__33 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_RW w__33 RW)))


def HaltingAllowed (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then (pure true)
    else
      (do
        (DoubleLockStatus ())) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      match ss with
      | .SS_NonSecure =>
        (do
          (ExternalInvasiveDebugEnabled ()))
      | .SS_Secure =>
        (do
          (ExternalSecureInvasiveDebugEnabled ()))
      | .SS_Root =>
        (do
          (ExternalRootInvasiveDebugEnabled ()))
      | .SS_Realm =>
        (do
          (ExternalRealmInvasiveDebugEnabled ())))


def AArch32_GenerateDebugExceptions (_ : Unit) : SailM Bool := do
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (AArch32_GenerateDebugExceptionsFrom w__0.EL ss)


def AArch64_GenerateDebugExceptions (_ : Unit) : SailM Bool := do
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  (AArch64_GenerateDebugExceptionsFrom w__0.EL ss w__1.D)


def SCTLR_read__2 (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_SCTLR_Type (← occLabel 666) ()) ) : SailM SCTLR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
      let r := (w__3 : (BitVec 32))
      let r : SCTLR_Type := (BitVec.update r 11 (Bit 1#1))
      let r : SCTLR_Type := (BitVec.update r 22 (Bit 1#1))
      (pure (r)))
  else
    (do
      let w__4 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
      let r := (w__4 : (BitVec 32))
      let r : SCTLR_Type := (BitVec.update r 11 (Bit 1#1))
      let r : SCTLR_Type := (BitVec.update r 22 (Bit 1#1))
      (pure (r)))


def IsCurrentSecurityState (ss : SecurityState) : SailM Bool := do
  let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  (pure ((BEq.beq w__0 ss)))


def AArch64_ReportException (except : ExceptionRecord) (target_el : (BitVec 2)) : SailM Unit := do
  let ec ← (( do (undefined_int_at (← occLabel 680) ()) ) : SailM Int )
  let il ← (( do (undefined_bitvector_at (← occLabel 681) 1) ) : SailM (BitVec 1) )
  let exceptype : Exception := except.exceptype
  let w__0 ← (( do (AArch64_ExceptionClass exceptype target_el) ) : SailM (Int × (BitVec 1)) )
  let (tup__0, tup__1) := (w__0 : (Int × (BitVec 1)))
  let ec : Int := tup__0
  let il : (BitVec 1) := tup__1
  let ec : Int := ec
  let iss : (BitVec 25) := except.syndrome
  let iss2 : (BitVec 24) := except.syndrome2
  let il : (BitVec 1) :=
    if ((((ec == (BitVec.toNat 0x24#8)) || ((ec == (BitVec.toNat 0x25#8)) : Bool)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               iss 24)])) == 0#1)) : Bool)
    then 1#1
    else il
  let il := il
  (ESR_set target_el
    (Mk_ESRType (((((Zeros (n := 8)) +++ iss2) +++ (integer_subrange ec 5 0)) +++ il) +++ iss)))
  if (((BEq.beq exceptype Exception_InstructionAbort) || ((BEq.beq exceptype Exception_PCAlignment) || ((BEq.beq
             exceptype Exception_DataAbort) || ((BEq.beq exceptype Exception_NV2DataAbort) || ((BEq.beq
                 exceptype Exception_NV2Watchpoint) || ((BEq.beq exceptype Exception_GPC) || (BEq.beq
                   exceptype Exception_Watchpoint))))))) : Bool)
  then
    (do
      (FAR_set target_el except.vaddress))
  else
    (do
      let w__1 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      (FAR_set target_el w__1))
  if (except.ipavalid : Bool)
  then
    (do
      let w__2 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
      writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__2 47 4
        (Sail.BitVec.extractLsb except.ipaddress 55 12))
      let w__5 ← (( do
        if ((← do
             (IsSecureEL2Enabled ())) : Bool)
        then
          (do
            let w__4 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((BEq.beq w__4 SS_Secure) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          let w__6 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
          writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__6 63 63 except.NS))
      else
        (do
          let w__7 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
          writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__7 63 63 0#1)))
  else
    (do
      if ((target_el == EL2) : Bool)
      then
        (do
          let w__8 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
          let w__9 ← (( do (__UNKNOWN_bits 44) ) : SailM (BitVec 44) )
          writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__8 47 4 w__9))
      else (pure (())))
  if (except.pavalid : Bool)
  then
    (do
      let faultaddr : (BitVec 64) := (Sail.BitVec.zeroExtend except.paddress.address 64)
      let w__10 ← (( do (HaveRME ()) ) : SailM Bool )
      let faultaddr : (BitVec 64) :=
        if (w__10 : Bool)
        then
          (let faultaddr : (BitVec 64) :=
            match except.paddress.paspace with
            | .PAS_Secure => (Sail.BitVec.updateSubrange faultaddr 63 62 0b00#2)
            | .PAS_NonSecure => (Sail.BitVec.updateSubrange faultaddr 63 62 0b10#2)
            | .PAS_Root => (Sail.BitVec.updateSubrange faultaddr 63 62 0b01#2)
            | .PAS_Realm => (Sail.BitVec.updateSubrange faultaddr 63 62 0b11#2)
          if ((BEq.beq exceptype Exception_GPC) : Bool)
          then (Sail.BitVec.updateSubrange faultaddr 11 0 (Zeros (n := 12)))
          else faultaddr)
        else
          (BitVec.update faultaddr 63
            (Bit
              (if ((BEq.beq except.paddress.paspace PAS_NonSecure) : Bool)
              then 1#1
              else 0#1)))
      (PFAR_set target_el faultaddr))
  else
    (do
      let w__14 ← (( do
        if ((← do
             (HavePFAR ())) : Bool)
        then (pure true)
        else
          (do
            (pure ((← do
                  (HaveRME ())) && ((target_el == EL3) : Bool)))) ) : SailM Bool )
      if (w__14 : Bool)
      then
        (do
          let w__15 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
          (PFAR_set target_el w__15))
      else (pure (())))


def VBAR_read__2 (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 705) 32) ) : SailM VBAR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg VBAR_S)
  else
    (do
      (VBAR_NS_read ()))


def WFETrapDelay (target_el : (BitVec 2)) : SailM (Bool × Int) := do
  let delay_enabled ← (( do (undefined_bool_at (← occLabel 728) ()) ) : SailM Bool )
  let delay ← (( do (undefined_int_at (← occLabel 729) ()) ) : SailM Int )
  let questionMark := target_el
  let (delay, delay_enabled) ← (( do
    if ((questionMark == EL1) : Bool)
    then
      (do
        let w__0 ← (( do (IsInHost ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let delay_enabled := (((_get_SCTLR_EL1_Type_TWEDEn w__1) == 1#1) : Bool)
            let w__2 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let delay : Int :=
              ((Int.shiftl 1
                (Sail.Int.toNatChecked (((BitVec.toNat (_get_SCTLR_EL1_Type_TWEDEL w__2)) +i 8)))) : Int)
            (pure ((delay, delay_enabled))))
        else
          (do
            let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let delay_enabled := (((_get_SCTLR_EL2_Type_TWEDEn w__3) == 1#1) : Bool)
            let w__4 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let delay : Int :=
              ((Int.shiftl 1
                (Sail.Int.toNatChecked (((BitVec.toNat (_get_SCTLR_EL2_Type_TWEDEL w__4)) +i 8)))) : Int)
            (pure ((delay, delay_enabled)))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            let w__5 ← (( do (EL2Enabled ()) ) : SailM Bool )
            ArmFull.assert w__5 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:10740.29-10740.30"
            let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let delay_enabled := (((_get_HCR_EL2_Type_TWEDEn w__6) == 1#1) : Bool)
            let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let delay : Int :=
              ((Int.shiftl 1
                (Sail.Int.toNatChecked (((BitVec.toNat (_get_HCR_EL2_Type_TWEDEL w__7)) +i 8)))) : Int)
            (pure ((delay, delay_enabled))))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let delay_enabled := (((_get_SCR_EL3_Type_TWEDEn w__8) == 1#1) : Bool)
                let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let delay : Int :=
                  ((Int.shiftl 1
                    (Sail.Int.toNatChecked (((BitVec.toNat (_get_SCR_EL3_Type_TWEDEL w__9)) +i 8)))) : Int)
                (pure ((delay, delay_enabled))))
            else (pure ((delay, delay_enabled))))) ) : SailM (Int × Bool) )
  let delay : Int := delay
  (pure ((delay_enabled, delay)))


def AArch64_ChkFeat (feat_select : (BitVec 64)) : SailM (BitVec 64) := do
  let feat_en : (BitVec 64) := (Zeros (n := 64))
  let w__3 ← (( do
    if ((← do
         (HaveGCS ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (GCSEnabled w__1.EL))
    else (pure false) ) : SailM Bool )
  let w__4 : (BitVec 1) :=
    if (w__3 : Bool)
    then 1#1
    else 0#1
  let feat_en := ((BitVec.update feat_en 0 (Bit w__4)) : (BitVec 64))
  (pure ((feat_select &&& (Complement.complement feat_en))))


def EffectiveTCMA (address : (BitVec 64)) (el : (BitVec 2)) : SailM (BitVec 1) := do
  let tcma ← (( do (undefined_bitvector_at (← occLabel 740) 1) ) : SailM (BitVec 1) )
  ArmFull.assert (HaveEL el) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11075.21-11075.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__0 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  ArmFull.assert (! w__0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11077.43-11077.44"
  let questionMark := regime
  if ((questionMark == EL1) : Bool)
  then
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
      then
        (do
          let w__1 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL1_Type_TCMA1 w__1))))
      else
        (do
          let w__2 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL1_Type_TCMA0 w__2)))))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          let w__6 ← (( do
            if ((← do
                 (HaveVirtHostExt ())) : Bool)
            then
              (do
                (ELIsInHost el))
            else (pure false) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
              then
                (do
                  let w__7 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL2_Type_TCMA1 w__7))))
              else
                (do
                  let w__8 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL2_Type_TCMA0 w__8)))))
          else
            (do
              let w__10 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              let tcma := ((_get_TCR_EL2_Type_TCMA w__10) : (BitVec 1))
              (pure (tcma))))
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              let w__11 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
              let tcma := ((_get_TCR_EL3_Type_TCMA w__11) : (BitVec 1))
              (pure (tcma)))
          else (pure (tcma))))


/-- Type quantifiers: k_is_instr : Bool -/
def EffectiveMTX (address : (BitVec 64)) (is_instr : Bool) (el : (BitVec 2)) : SailM (BitVec 1) := do
  let mtx ← (( do (undefined_bitvector_at (← occLabel 741) 1) ) : SailM (BitVec 1) )
  ArmFull.assert (HaveEL el) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11109.21-11109.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__0 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  ArmFull.assert (! w__0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11111.43-11111.44"
  let w__2 ← (( do
    (pure ((← do
          let w__1 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
          (pure (((! w__1) : Bool)))) || (is_instr : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (0#1))
  else
    (do
      let questionMark := regime
      if ((questionMark == EL1) : Bool)
      then
        (do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
          then
            (do
              let w__3 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX1 w__3))))
          else
            (do
              let w__4 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX0 w__4)))))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__8 ← (( do
                if ((← do
                     (HaveVirtHostExt ())) : Bool)
                then
                  (do
                    (ELIsInHost el))
                else (pure false) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
                  then
                    (do
                      let w__9 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_MTX1 w__9))))
                  else
                    (do
                      let w__10 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_MTX0 w__10)))))
              else
                (do
                  let w__12 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                  let mtx := ((_get_TCR_EL2_Type_MTX w__12) : (BitVec 1))
                  (pure (mtx))))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                  let mtx := ((_get_TCR_EL3_Type_MTX w__13) : (BitVec 1))
                  (pure (mtx)))
              else (pure (mtx)))))


def AltPARTIDspace (el : (BitVec 2)) (security : SecurityState) (primaryPIdSpace : PARTIDspaceType) : SailM PARTIDspaceType := do
  match security with
  | .SS_NonSecure =>
    (do
      ArmFull.assert (el != EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11334.26-11334.27"
      (pure (primaryPIdSpace)))
  | .SS_Secure =>
    (do
      ArmFull.assert (el != EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11338.26-11338.27"
      if ((BEq.beq primaryPIdSpace PIdSpace_NonSecure) : Bool)
      then (pure (primaryPIdSpace))
      else
        (do
          (AltPIdSecure el primaryPIdSpace)))
  | .SS_Root =>
    (do
      ArmFull.assert (el == EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11345.26-11345.27"
      let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      if (((_get_MPAM3_EL3_Type_ALTSP_EL3 w__2) == 1#1) : Bool)
      then
        (do
          let w__3 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
          let w__4 : PARTIDspaceType :=
            if (((_get_MPAM3_EL3_Type_RT_ALTSP_NS w__3) == 1#1) : Bool)
            then PIdSpace_NonSecure
            else PIdSpace_Secure
          (pure (w__4)))
      else (pure (primaryPIdSpace)))
  | .SS_Realm =>
    (do
      ArmFull.assert (el != EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:11357.26-11357.27"
      (AltPIdRealm el primaryPIdSpace))


end ArmFull.Functions
