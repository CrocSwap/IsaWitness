module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0137
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0176
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0190
public import ArmFull.Fn.M0193
public import ArmFull.Fn.M0194 set_option backward.proofsInPublic true @[expose] public section

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
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:49755.45-49755.46"
      (ICC_AP1R_S_set (Sail.Int.toNatChecked (n)) r))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:49758.45-49758.46"
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


def decode_aarch32_instrs_DSB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_DSB_Op_A_txt option_name))
  else (pure (()))


def decode_aarch32_instrs_DSB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_DSB_Op_A_txt option_name))
  else (pure (()))


/-- Type quantifiers: k_affectA : Bool, k_affectF : Bool, k_affectI : Bool, k_changemode : Bool, k_disable
  : Bool, k_enable : Bool -/
def execute_aarch32_instrs_CPS_OpT_AS_txt (affectA : Bool) (affectF : Bool) (affectI : Bool) (changemode : Bool) (disable : Bool) (enable : Bool) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL != EL0) : Bool)
  then
    (do
      if (enable : Bool)
      then
        (do
          if (affectA : Bool)
          then
            (do
              let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__1 with A := 0#1 })
          else (pure (()))
          if (affectI : Bool)
          then
            (do
              let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__2 with I := 0#1 })
          else (pure (()))
          if (affectF : Bool)
          then
            (do
              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__3 with F := 0#1 })
          else (pure (())))
      else (pure (()))
      if (disable : Bool)
      then
        (do
          if (affectA : Bool)
          then
            (do
              let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__4 with A := 1#1 })
          else (pure (()))
          if (affectI : Bool)
          then
            (do
              let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__5 with I := 1#1 })
          else (pure (()))
          if (affectF : Bool)
          then
            (do
              let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__6 with F := 1#1 })
          else (pure (())))
      else (pure (()))
      if (changemode : Bool)
      then
        (do
          (AArch32_WriteModeByInstr mode))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: increment_name : Int -/
def IncrementInstructionCounter (increment_name : Int) : SailM Unit := do
  let w__0 ← (( do (CountPMUEvents INSTRUCTION_COUNTER_ID) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg PMICNTR_EL0 ) : SailM (BitVec 64) )
      let old_value : Int := (BitVec.toNat w__1)
      let new_value : Int := (old_value +i increment_name)
      writeReg PMICNTR_EL0 (Mk_PMICNTR_EL0_Type (integer_subrange new_value 63 0))
      if (((BitVec.setWidth 1 (BitVec.join1 [(integer_access old_value 64)])) != (BitVec.setWidth 1 (BitVec.join1 [(integer_access
               new_value 64)]))) : Bool)
      then
        (do
          let w__2 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
          writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__2 32 32 1#1)
          let w__3 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
          writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__3 32 32 1#1))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: k_IsInstr : Bool -/
def AddrTop (address : (BitVec 64)) (IsInstr : Bool) (el : (BitVec 2)) : SailM Int := do
  let w__0 ← (( do (HaveEL el) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:6128.21-6128.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (31))
  else
    (do
      let w__2 ← (( do (EffectiveTBI address IsInstr el) ) : SailM (BitVec 1) )
      let w__3 : Int :=
        if ((w__2 == 1#1) : Bool)
        then 55
        else 63
      (pure (w__3)))


/-- Type quantifiers: n : Int -/
def R_read (n : Int) : SailM (BitVec 32) := do
  let offset ← (( do (undefined_int_at (← occLabel 573) ()) ) : SailM Int )
  if ((n == 15) : Bool)
  then
    (do
      let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
      let offset : Int :=
        if ((BEq.beq w__0 InstrSet_A32) : Bool)
        then 8
        else 4
      let w__1 ← (( do readReg _PC ) : SailM (BitVec 64) )
      (pure ((BitVec.addInt (Sail.BitVec.extractLsb w__1 31 0) offset))))
  else
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      (Rmode_read n w__2.M))


/-- Type quantifiers: k_N : Nat, k_conditional : Bool, k_is_isb : Bool, k_taken_flag : Bool, k_N ≥
  0 -/
def SPEBranch__1 (target : (BitVec k_N)) (branch_type : BranchType) (conditional : Bool) (taken_flag : Bool) (is_isb : Bool) : SailM Unit := do
  let is_direct ← (( do (undefined_bool_at (← occLabel 593) ()) ) : SailM Bool )
  let collect_prev_br ← (( do (undefined_bool_at (← occLabel 594) ()) ) : SailM Bool )
  let collect_prev_br_eret ← (( do (__IMPDEF_boolean "SPE prev br on eret") ) : SailM Bool )
  let collect_prev_br_exception ← (( do (__IMPDEF_boolean "SPE prev br on exception") ) : SailM
    Bool )
  let collect_prev_br_isb ← (( do (__IMPDEF_boolean "SPE prev br on isb") ) : SailM Bool )
  let collect_prev_br : Bool :=
    match branch_type with
    | .BranchType_EXCEPTION => collect_prev_br_exception
    | .BranchType_ERET => collect_prev_br_eret
    | _ => ((! is_isb) || collect_prev_br_isb)
  let collect_prev_br := collect_prev_br
  let w__4 ← (( do
    (pure ((← do
          if ((← do
               if ((taken_flag : Bool) : Bool)
               then
                 (do
                   let w__0 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
                   (pure (((! (IsZero (_get_PMSIDR_EL1_Type_PBT w__0))) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              (StatisticalProfilingEnabled ()))
          else (pure false)) && collect_prev_br)) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do readReg SPESampleInFlight ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          let previous_target ← (( do readReg SPESamplePreviousBranchAddress ) : SailM (BitVec 64)
            )
          let w__6 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
          let w__7 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
          writeReg SPESampleAddress (vectorUpdate w__6 SPEAddrPosPrevBranchTarget
            (Sail.BitVec.updateSubrange (GetElem?.getElem! w__7 SPEAddrPosPrevBranchTarget) 63 0
              (Sail.BitVec.extractLsb previous_target 63 0)))
          let previous_branch_valid ← (( do readReg SPESamplePreviousBranchAddressValid ) : SailM
            Bool )
          let w__8 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
          writeReg SPESampleAddressValid (vectorUpdate w__8 SPEAddrPosPrevBranchTarget
            previous_branch_valid))
      else (pure (()))
      ArmFull.assert (55 <b (Sail.BitVec.length target)) "sail-inputs/03-v8_base.sail:6728.34-6728.35"
      let w__9 ← (( do readReg SPESamplePreviousBranchAddress ) : SailM (BitVec 64) )
      writeReg SPESamplePreviousBranchAddress (Sail.BitVec.updateSubrange w__9 55 0
        (Sail.BitVec.extractLsb target 55 0))
      let ns ← (( do (undefined_bitvector_at (← occLabel 595) 1) ) : SailM (BitVec 1) )
      let nse ← (( do (undefined_bitvector_at (← occLabel 596) 1) ) : SailM (BitVec 1) )
      let w__10 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      let (ns, nse) ← (( do
        match w__10 with
        | .SS_Secure =>
          (let ns : (BitVec 1) := 0#1
          let nse : (BitVec 1) := 0#1
          (pure ((ns, nse))))
        | .SS_NonSecure =>
          (let ns : (BitVec 1) := 1#1
          let nse : (BitVec 1) := 0#1
          (pure ((ns, nse))))
        | .SS_Realm =>
          (let ns : (BitVec 1) := 1#1
          let nse : (BitVec 1) := 1#1
          (pure ((ns, nse))))
        | _ =>
          (do
            (Unreachable ())
            (pure ((ns, nse)))) ) : SailM ((BitVec 1) × (BitVec 1)) )
      let w__11 ← (( do readReg SPESamplePreviousBranchAddress ) : SailM (BitVec 64) )
      writeReg SPESamplePreviousBranchAddress (BitVec.update w__11 63 (Bit ns))
      let w__12 ← (( do readReg SPESamplePreviousBranchAddress ) : SailM (BitVec 64) )
      writeReg SPESamplePreviousBranchAddress (BitVec.update w__12 60 (Bit nse))
      let w__13 ← (( do readReg SPESamplePreviousBranchAddress ) : SailM (BitVec 64) )
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg SPESamplePreviousBranchAddress (Sail.BitVec.updateSubrange w__13 62 61 w__14.EL)
      writeReg SPESamplePreviousBranchAddressValid true)
  else (pure (()))
  let w__15 ← (( do (StatisticalProfilingEnabled ()) ) : SailM Bool )
  if ((! w__15) : Bool)
  then
    (do
      if (taken_flag : Bool)
      then
        (do
          writeReg SPESamplePreviousBranchAddressValid false)
      else (pure (())))
  else
    (do
      let w__16 ← (( do readReg SPESampleInFlight ) : SailM Bool )
      if (w__16 : Bool)
      then
        (do
          let is_direct : Bool :=
            ((BEq.beq branch_type BranchType_DIR) || (BEq.beq branch_type BranchType_DIRCALL))
          writeReg SPESampleClass 0b10#2
          let w__17 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
          writeReg SPESampleSubclass (BitVec.update w__17 1
            (Bit
              (if (is_direct : Bool)
              then 0#1
              else 1#1)))
          let w__18 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
          writeReg SPESampleSubclass (BitVec.update w__18 0
            (Bit
              (if (conditional : Bool)
              then 1#1
              else 0#1)))
          writeReg SPESampleOpType OpType_Branch
          if (taken_flag : Bool)
          then
            (do
              ArmFull.assert (55 <b (Sail.BitVec.length target)) "sail-inputs/03-v8_base.sail:6767.38-6767.39"
              let w__19 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              let w__20 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              writeReg SPESampleAddress (vectorUpdate w__19 SPEAddrPosBranchTarget
                (Sail.BitVec.updateSubrange (GetElem?.getElem! w__20 SPEAddrPosBranchTarget) 55 0
                  (Sail.BitVec.extractLsb target 55 0)))
              let ns ← (( do (undefined_bitvector_at (← occLabel 597) 1) ) : SailM (BitVec 1) )
              let nse ← (( do (undefined_bitvector_at (← occLabel 598) 1) ) : SailM (BitVec 1) )
              let w__21 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
              let (ns, nse) ← (( do
                match w__21 with
                | .SS_Secure =>
                  (let ns : (BitVec 1) := 0#1
                  let nse : (BitVec 1) := 0#1
                  (pure ((ns, nse))))
                | .SS_NonSecure =>
                  (let ns : (BitVec 1) := 1#1
                  let nse : (BitVec 1) := 0#1
                  (pure ((ns, nse))))
                | .SS_Realm =>
                  (let ns : (BitVec 1) := 1#1
                  let nse : (BitVec 1) := 1#1
                  (pure ((ns, nse))))
                | _ =>
                  (do
                    (Unreachable ())
                    (pure ((ns, nse)))) ) : SailM ((BitVec 1) × (BitVec 1)) )
              let w__22 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              let w__23 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              writeReg SPESampleAddress (vectorUpdate w__22 SPEAddrPosBranchTarget
                (BitVec.update (GetElem?.getElem! w__23 SPEAddrPosBranchTarget) 63 (Bit ns)))
              let w__24 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              let w__25 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              writeReg SPESampleAddress (vectorUpdate w__24 SPEAddrPosBranchTarget
                (BitVec.update (GetElem?.getElem! w__25 SPEAddrPosBranchTarget) 60 (Bit nse)))
              let w__26 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              let w__27 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
              let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg SPESampleAddress (vectorUpdate w__26 SPEAddrPosBranchTarget
                (Sail.BitVec.updateSubrange (GetElem?.getElem! w__27 SPEAddrPosBranchTarget) 62 61
                  w__28.EL))
              let w__29 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
              writeReg SPESampleAddressValid (vectorUpdate w__29 SPEAddrPosBranchTarget true))
          else (pure (()))
          let w__30 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
          writeReg SPESampleEvents (BitVec.update w__30 6
            (Bit
              (if ((! taken_flag) : Bool)
              then 1#1
              else 0#1))))
      else (pure (())))


def CurrentVL_read (_ : Unit) : SailM Int := do
  let w__2 ← (( do
    if ((← do
         (HaveSME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.SM == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let vl ← (( do
    if (w__2 : Bool)
    then
      (do
        (CurrentSVL_read ()))
    else
      (do
        (CurrentNSVL_read ())) ) : SailM Int )
  (__ArmCertRequireVectorLength vl)


def AArch32_IsFPEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  let w__1 ← (( do
    if (((el == EL0) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (ELUsingAArch32 EL1) ) : SailME Bool Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailME Bool Bool )
  if (w__1 : Bool)
  then
    (do
      (AArch64_IsFPEnabled el))
  else
    (do
      let w__7 ← (( do
        if ((← do
             if ((← do
                  (HaveEL EL3)) : Bool)
             then
               (do
                 (ELUsingAArch32 EL3))
             else (pure false)) : Bool)
        then
          (do
            let w__6 ← (( do (CurrentSecurityState ()) ) : SailME Bool SecurityState )
            (pure (((BEq.beq w__6 SS_NonSecure) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__7 : Bool)
      then
        (do
          let w__8 ← (( do readReg NSACR ) : SailME Bool (BitVec 32) )
          if (((_get_NSACR_Type_cp10 w__8) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      if (((el == EL0) || (el == EL1)) : Bool)
      then
        (do
          let disabled ← (( do (undefined_bool_at (← occLabel 619) ()) ) : SailME Bool Bool )
          let w__9 ← (( do (CPACR_read__1 ()) ) : SailME Bool (BitVec 32) )
          let disabled ← (( do
            match (BitVec.setWidth 2 (_get_CPACR_Type_cp10 w__9)) with
            | 0b00 => (pure (true))
            | 0b01 =>
              (let disabled : Bool := (el == EL0)
              (pure (disabled)))
            | 0b10 =>
              (do
                (ConstrainUnpredictableBool Unpredictable_RESCPACR))
            | _ => (pure (false)) ) : SailME Bool Bool )
          let disabled := disabled
          if (disabled : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      let w__12 ← (( do
        if ((((el == EL0) || ((el == EL1) || (el == EL2))) : Bool) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailME Bool Bool )
      if (w__12 : Bool)
      then
        (do
          let w__13 ← (( do (ELUsingAArch32 EL2) ) : SailME Bool Bool )
          if ((! w__13) : Bool)
          then
            (do
              let w__14 ← (( do (AArch64_IsFPEnabled EL2) ) : SailME Bool Bool )
              SailME.throw (w__14 : Bool))
          else
            (do
              let w__15 ← (( do (HCPTR_read ()) ) : SailME Bool (BitVec 32) )
              if (((_get_HCPTR_Type_TCP10 w__15) == 1#1) : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (()))))
      else (pure (()))
      let w__18 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailME Bool Bool )
            (pure (((! w__17) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__18 : Bool)
      then
        (do
          let w__19 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL3_Type_TFP w__19) == 1#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


end ArmFull.Functions
