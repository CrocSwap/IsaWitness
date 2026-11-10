import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0063
import ArmFull.Fn.M0071
import ArmFull.Fn.M0079
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0137
import ArmFull.Fn.M0144
import ArmFull.Fn.M0176
import ArmFull.Fn.M0178
import ArmFull.Fn.M0182
import ArmFull.Fn.M0186
import ArmFull.Fn.M0189

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

def SPSRaccessValid (SYSm : (BitVec 5)) (mode : (BitVec 5)) : SailM Unit := do
  match SYSm with
  | 0b01110 =>
    (do
      if ((mode == M32_FIQ) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10000 =>
    (do
      if ((mode == M32_IRQ) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10010 =>
    (do
      if ((mode == M32_Svc) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10100 =>
    (do
      if ((mode == M32_Abort) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10110 =>
    (do
      if ((mode == M32_Undef) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b11100 =>
    (do
      let w__1 ← (( do
        if ((((! (HaveEL EL3)) || (mode == M32_Monitor)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne w__0 SS_Secure) : Bool)))) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b11110 =>
    (do
      if (((! (HaveEL EL2)) || (mode != M32_Monitor)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | _ => sailThrow ((Error_Unpredictable ()))


def AArch32_ClearEventCounters (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch64_ClearEventCounters ()))
  else
    (do
      let counters ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert (0 ≤b idx) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:43512.45-43512.46"
                ArmFull.assert (idx <b 31) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:43513.45-43513.46"
                (PMEVCNTR_set (Sail.Int.toNatChecked (idx)) (Zeros (n := 32)))
            (pure loop_vars)))
      else (pure (())))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_EL1_read (n : Int) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_AP1R_EL1_Type (← occLabel 2815) ()) ) : SailM ICC_AP1R_EL1_Type )
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
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:44767.45-44767.46"
      let w__3 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
      let r := ((GetElem?.getElem! w__3 (Sail.Int.toNatChecked (n))) : (BitVec 64))
      (pure (r)))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:44770.45-44770.46"
      let w__4 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
      let r := ((GetElem?.getElem! w__4 (Sail.Int.toNatChecked (n))) : (BitVec 64))
      (pure (r)))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_EL1_set (n : Int) (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_AP1R_EL1_Type := value_name
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
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:44781.45-44781.46"
      let w__3 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
      writeReg ICC_AP1R_EL1_S (vectorUpdate w__3 (Sail.Int.toNatChecked (n)) r))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:44784.45-44784.46"
      let w__4 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
      writeReg ICC_AP1R_EL1_NS (vectorUpdate w__4 (Sail.Int.toNatChecked (n)) r))


def CNTP_CVAL_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTP_CVAL_Type := value_name
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
      writeReg CNTP_CVAL_S r)
  else
    (do
      (CNTP_CVAL_NS_write r))


def AIFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2835) 32) ) : SailM AIFSR_Type )
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
      readReg AIFSR_S)
  else
    (do
      (AIFSR_NS_read ()))


def AIFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AIFSR_Type := value_name
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
      writeReg AIFSR_S r)
  else
    (do
      (AIFSR_NS_write r))


def DACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DACR_Type := value_name
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
      writeReg DACR_S r)
  else
    (do
      (DACR_NS_write r))


def TPIDRURW_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2836) 32) ) : SailM TPIDRURW_Type )
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
      readReg TPIDRURW_S)
  else
    (do
      (TPIDRURW_NS_read ()))


def TPIDRURW_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURW_Type := value_name
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
      writeReg TPIDRURW_S r)
  else
    (do
      (TPIDRURW_NS_write r))


def ADFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2837) 32) ) : SailM ADFSR_Type )
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
      readReg ADFSR_S)
  else
    (do
      (ADFSR_NS_read ()))


def ADFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ADFSR_Type := value_name
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
      writeReg ADFSR_S r)
  else
    (do
      (ADFSR_NS_write r))


def TPIDRURO_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2838) 32) ) : SailM TPIDRURO_Type )
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
      readReg TPIDRURO_S)
  else
    (do
      (TPIDRURO_NS_read ()))


def TPIDRURO_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURO_Type := value_name
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
      writeReg TPIDRURO_S r)
  else
    (do
      (TPIDRURO_NS_write r))


def ACTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2840) 32) ) : SailM ACTLR_Type )
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
      readReg ACTLR_S)
  else
    (do
      (ACTLR_NS_read ()))


def ACTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR_Type := value_name
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
      writeReg ACTLR_S r)
  else
    (do
      (ACTLR_NS_write r))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_read (n : Int) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2843) 32) ) : SailM ICC_AP1R_Type )
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
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:49731.45-49731.46"
      (ICC_AP1R_S_read (Sail.Int.toNatChecked (n))))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:49734.45-49734.46"
      (ICC_AP1R_NS_read (Sail.Int.toNatChecked (n))))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_set (n : Int) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP1R_Type := value_name
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
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:49745.45-49745.46"
      (ICC_AP1R_S_set (Sail.Int.toNatChecked (n)) r))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:49748.45-49748.46"
      (ICC_AP1R_NS_set (Sail.Int.toNatChecked (n)) r))


def AMAIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2845) 32) ) : SailM AMAIR0_Type )
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
      readReg AMAIR0_S)
  else
    (do
      (AMAIR0_NS_read ()))


def AMAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR0_Type := value_name
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
      writeReg AMAIR0_S r)
  else
    (do
      (AMAIR0_NS_write r))


def ACTLR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2850) 32) ) : SailM ACTLR2_Type )
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
      readReg ACTLR2_S)
  else
    (do
      (ACTLR2_NS_read ()))


def ACTLR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR2_Type := value_name
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
      writeReg ACTLR2_S r)
  else
    (do
      (ACTLR2_NS_write r))


def __set_SCTLR (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
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
      (__set_SCTLR_S r))
  else
    (do
      (__set_SCTLR_NS r))


def __set_CNTP_CTL (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
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
      (__set_CNTP_CTL_S r))
  else
    (do
      (__set_CNTP_CTL_NS r))


def TPIDRPRW_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2851) 32) ) : SailM TPIDRPRW_Type )
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
      readReg TPIDRPRW_S)
  else
    (do
      (TPIDRPRW_NS_read ()))


def TPIDRPRW_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRPRW_Type := value_name
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
      writeReg TPIDRPRW_S r)
  else
    (do
      (TPIDRPRW_NS_write r))


def IFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2852) 32) ) : SailM IFAR_Type )
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
      (IFAR_S_read ()))
  else
    (do
      (IFAR_NS_read ()))


def CONTEXTIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CONTEXTIDR_Type := value_name
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
      writeReg CONTEXTIDR_S r)
  else
    (do
      (CONTEXTIDR_NS_write r))


def DFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2854) 32) ) : SailM DFAR_Type )
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
      (DFAR_S_read ()))
  else
    (do
      (DFAR_NS_read ()))


def AMAIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2856) 32) ) : SailM AMAIR1_Type )
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
      readReg AMAIR1_S)
  else
    (do
      (AMAIR1_NS_read ()))


def AMAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR1_Type := value_name
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
      writeReg AMAIR1_S r)
  else
    (do
      (AMAIR1_NS_write r))


end ArmFull.Functions
