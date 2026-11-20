module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0008
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0187 set_option backward.proofsInPublic true @[expose] public section

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

def IsSMEEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  let disabled ← (( do (undefined_bool_at (← occLabel 621) ()) ) : SailME Bool Bool )
  let w__0 ← (( do (ELUsingAArch32 el) ) : SailME Bool Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if ((((el == EL0) || (el == EL1)) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (IsInHost ()) ) : SailME Bool Bool )
            (pure (((! w__1) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      let disabled ← (( do
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg CPACR_EL1 ) : SailME Bool (BitVec 64) )
            let b__0 := (_get_CPACR_EL1_Type_SMEN w__3)
            let disabled : Bool :=
              if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
              then true
              else
                (match b__0 with
                | 0b01 => (el == EL0)
                | _ => false)
            if (disabled : Bool)
            then
              (do
                SailME.throw (false : Bool))
            else (pure (()))
            (pure (disabled)))
        else (pure (disabled)) ) : SailME Bool Bool )
      let w__5 ← (( do
        if ((((el == EL0) || ((el == EL1) || (el == EL2))) : Bool) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailME Bool Bool )
      if (w__5 : Bool)
      then
        (do
          let w__8 ← (( do
            if ((← do
                 (HaveVirtHostExt ())) : Bool)
            then
              (do
                let w__7 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_E2H w__7) == 1#1) : Bool))))
            else (pure false) ) : SailME Bool Bool )
          if (w__8 : Bool)
          then
            (do
              let w__9 ← (( do readReg CPTR_EL2 ) : SailME Bool (BitVec 64) )
              let b__1 := (_get_CPTR_EL2_Type_SMEN w__9)
              let disabled ← (( do
                if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                then (pure (true))
                else
                  (do
                    match b__1 with
                    | 0b01 =>
                      (do
                        if (((el == EL0) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__10) == 1#1) : Bool))))
                        else (pure false))
                    | _ => (pure (false))) ) : SailME Bool Bool )
              if (disabled : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (())))
          else
            (do
              let w__12 ← (( do readReg CPTR_EL2 ) : SailME Bool (BitVec 64) )
              if (((_get_CPTR_EL2_Type_TSM w__12) == 1#1) : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (()))))
      else (pure (()))
      let w__13 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL3_Type_ESM w__14) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


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
      let w__27 ← (( do
        if ((← do
             let w__21 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__21) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (HaveEL EL3)) : Bool)
                 then
                   (do
                     let w__23 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
                     (pure ((((_get_SCRType_NS w__23) == 0#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__25 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
                (pure (((! w__25) : Bool))))
            else (pure false)) ) : SailM Bool )
      let RW ← (( do
        if (w__27 : Bool)
        then
          (let RW : (BitVec 4) :=
            (BitVec.update RW 2 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 1)]))))
          (pure (RW)))
        else
          (do
            let w__28 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
            let w__29 : (BitVec 1) :=
              if (w__28 : Bool)
              then 0#1
              else 1#1
            let RW := ((BitVec.update RW 2 (Bit w__29)) : (BitVec 4))
            (pure (RW))) ) : SailM (BitVec 4) )
      let w__30 ← (( do (HaveEL EL3) ) : SailM Bool )
      let RW ← (( do
        if ((! w__30) : Bool)
        then
          (let RW : (BitVec 4) :=
            (BitVec.update RW 3 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 2)]))))
          (pure (RW)))
        else
          (do
            let w__31 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            let w__32 : (BitVec 1) :=
              if (w__31 : Bool)
              then 0#1
              else 1#1
            let RW := ((BitVec.update RW 3 (Bit w__32)) : (BitVec 4))
            (pure (RW))) ) : SailM (BitVec 4) )
      let RW ← (( do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 3)])) == 0#1) : Bool)
        then
          (do
            let w__33 ← (( do (__UNKNOWN_bits 3) ) : SailM (BitVec 3) )
            let RW := ((Sail.BitVec.updateSubrange RW 2 0 w__33) : (BitVec 4))
            (pure (RW)))
        else
          (do
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 2)])) == 0#1) : Bool)
            then
              (do
                let w__34 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
                let RW := ((Sail.BitVec.updateSubrange RW 1 0 w__34) : (BitVec 4))
                (pure (RW)))
            else
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access RW 1)])) == 0#1) : Bool)
                then
                  (do
                    let w__35 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                    let RW := ((BitVec.update RW 0 (Bit w__35)) : (BitVec 4))
                    (pure (RW)))
                else (pure (RW)))) ) : SailM (BitVec 4) )
      let w__36 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_RW w__36 RW)))


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
            ArmFull.assert w__5 "sail-inputs/03-v8_base.sail:10753.29-10753.30"
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
  let w__0 ← (( do (HaveEL el) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:11088.21-11088.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:11090.43-11090.44"
  let questionMark := regime
  if ((questionMark == EL1) : Bool)
  then
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
      then
        (do
          let w__2 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL1_Type_TCMA1 w__2))))
      else
        (do
          let w__3 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL1_Type_TCMA0 w__3)))))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          let w__7 ← (( do
            if ((← do
                 (HaveVirtHostExt ())) : Bool)
            then
              (do
                (ELIsInHost el))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
              then
                (do
                  let w__8 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL2_Type_TCMA1 w__8))))
              else
                (do
                  let w__9 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL2_Type_TCMA0 w__9)))))
          else
            (do
              let w__11 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              let tcma := ((_get_TCR_EL2_Type_TCMA w__11) : (BitVec 1))
              (pure (tcma))))
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              let w__12 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
              let tcma := ((_get_TCR_EL3_Type_TCMA w__12) : (BitVec 1))
              (pure (tcma)))
          else (pure (tcma))))


end ArmFull.Functions
