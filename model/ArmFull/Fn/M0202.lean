import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0113
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0189
import ArmFull.Fn.M0192
import ArmFull.Fn.M0193
import ArmFull.Fn.M0194
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196

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


def decode_tcommit_aarch64_instrs_system_tme_tcommit (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_system_tme_tcommit ())


def decode_ttest_aarch64_instrs_system_tme_ttest (Rt : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  (execute_aarch64_instrs_system_tme_ttest (Sail.Int.toNatChecked (t)))


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
  ArmFull.assert (HaveEL el) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6128.21-6128.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__0 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (31))
  else
    (do
      let w__1 ← (( do (EffectiveTBI address IsInstr el) ) : SailM (BitVec 1) )
      let w__2 : Int :=
        if ((w__1 == 1#1) : Bool)
        then 55
        else 63
      (pure (w__2)))


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
      ArmFull.assert (55 <b (Sail.BitVec.length target)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6728.34-6728.35"
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
              ArmFull.assert (55 <b (Sail.BitVec.length target)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6767.38-6767.39"
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
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.SM == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (SVL))
  else
    (do
      (CurrentNSVL_read ()))


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
      let w__6 ← (( do
        if ((← do
             if (((HaveEL EL3) : Bool) : Bool)
             then
               (do
                 (ELUsingAArch32 EL3))
             else (pure false)) : Bool)
        then
          (do
            let w__5 ← (( do (CurrentSecurityState ()) ) : SailME Bool SecurityState )
            (pure (((BEq.beq w__5 SS_NonSecure) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__6 : Bool)
      then
        (do
          let w__7 ← (( do readReg NSACR ) : SailME Bool (BitVec 32) )
          if (((_get_NSACR_Type_cp10 w__7) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      if (((el == EL0) || (el == EL1)) : Bool)
      then
        (do
          let disabled ← (( do (undefined_bool_at (← occLabel 619) ()) ) : SailME Bool Bool )
          let w__8 ← (( do (CPACR_read__1 ()) ) : SailME Bool (BitVec 32) )
          let disabled ← (( do
            match (BitVec.setWidth 2 (_get_CPACR_Type_cp10 w__8)) with
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
      let w__11 ← (( do
        if ((((el == EL0) || ((el == EL1) || (el == EL2))) : Bool) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailME Bool Bool )
      if (w__11 : Bool)
      then
        (do
          let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailME Bool Bool )
          if ((! w__12) : Bool)
          then
            (do
              let w__13 ← (( do (AArch64_IsFPEnabled EL2) ) : SailME Bool Bool )
              SailME.throw (w__13 : Bool))
          else
            (do
              let w__14 ← (( do (HCPTR_read ()) ) : SailME Bool (BitVec 32) )
              if (((_get_HCPTR_Type_TCP10 w__14) == 1#1) : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (()))))
      else (pure (()))
      let w__16 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__15 ← (( do (ELUsingAArch32 EL3) ) : SailME Bool Bool )
            (pure (((! w__15) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__16 : Bool)
      then
        (do
          let w__17 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL3_Type_TFP w__17) == 1#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


def IsSVEEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         (HaveSME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.SM == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (IsSMEEnabled el))
  else
    (do
      let w__4 ← (( do (HaveSVE ()) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          (IsOriginalSVEEnabled el))
      else (pure (false)))


def ShouldBRBEFreeze (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (BranchRecordAllowed w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then (pure (false))
  else
    (do
      let check_e : Bool := false
      let check_cnten : Bool := false
      let check_inten : Bool := false
      let exclude_sync : Bool := false
      let exclude_cyc : Bool := true
      let include_lo_name ← (( do (undefined_bool_at (.site 628) ()) ) : SailM Bool )
      let include_hi_name ← (( do (undefined_bool_at (.site 629) ()) ) : SailM Bool )
      let (include_hi_name, include_lo_name) ← (( do
        if ((HaveEL EL2) : Bool)
        then
          (do
            let w__2 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
            let include_lo_name := (((_get_BRBCR_EL1_Type_FZP w__2) == 1#1) : Bool)
            let w__3 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
            let include_hi_name := (((_get_BRBCR_EL2_Type_FZP w__3) == 1#1) : Bool)
            (pure ((include_hi_name, include_lo_name))))
        else
          (let include_lo_name : Bool := true
          let include_hi_name : Bool := true
          (pure ((include_hi_name, include_lo_name)))) ) : SailM (Bool × Bool) )
      (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name
        exclude_cyc exclude_sync))


/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def DebugExceptionReturnSS (spsr : (BitVec k_N)) : SailM (BitVec 1) := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (Halted ())) : Bool)
         then (pure true)
         else
           (do
             (Restarting ()))) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__3.EL != EL0) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8493.55-8493.56"
  let enabled_at_source ← (( do (undefined_bool_at (← occLabel 655) ()) ) : SailM Bool )
  let w__5 ← (( do (Restarting ()) ) : SailM Bool )
  let enabled_at_source ← (( do
    if (w__5 : Bool)
    then (pure (false))
    else
      (do
        let w__6 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        if (w__6 : Bool)
        then
          (do
            (AArch32_GenerateDebugExceptions ()))
        else
          (do
            (AArch64_GenerateDebugExceptions ()))) ) : SailM Bool )
  let valid_name ← (( do (undefined_bool_at (← occLabel 656) ()) ) : SailM Bool )
  let dest_el ← (( do (undefined_bitvector_at (← occLabel 657) 2) ) : SailM (BitVec 2) )
  let w__9 ← (( do (IllegalExceptionReturn spsr) ) : SailM Bool )
  let dest_el ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
        let dest_el := (w__10.EL : (BitVec 2))
        (pure (dest_el)))
    else
      (do
        let w__11 ← (( do (ELFromSPSR spsr) ) : SailM (Bool × (BitVec 2)) )
        let (tup__0, tup__1) := (w__11 : (Bool × (BitVec 2)))
        let valid_name : Bool := tup__0
        let dest_el : (BitVec 2) := tup__1
        ArmFull.assert valid_name "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8508.25-8508.26"
        (pure (dest_el))) ) : SailM (BitVec 2) )
  let dest_ss ← (( do (SecurityStateAtEL dest_el) ) : SailM SecurityState )
  let mask ← (( do (undefined_bitvector_at (← occLabel 658) 1) ) : SailM (BitVec 1) )
  let enabled_at_dest ← (( do (undefined_bool_at (← occLabel 659) ()) ) : SailM Bool )
  let dest_using_32 ← (( do
    if ((dest_el == EL0) : Bool)
    then (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 4)])) == 1#1)))
    else
      (do
        (ELUsingAArch32 dest_el)) ) : SailM Bool )
  let enabled_at_dest ← (( do
    if (dest_using_32 : Bool)
    then
      (do
        (AArch32_GenerateDebugExceptionsFrom dest_el dest_ss))
    else
      (do
        ArmFull.assert (9 <b (Sail.BitVec.length spsr)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8518.33-8518.34"
        let mask : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 9)]))
        (AArch64_GenerateDebugExceptionsFrom dest_el dest_ss mask)) ) : SailM Bool )
  let ELd ← (( do (DebugTargetFrom dest_ss) ) : SailM (BitVec 2) )
  let SS_bit ← (( do (undefined_bitvector_at (← occLabel 660) 1) ) : SailM (BitVec 1) )
  let w__19 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     let w__15 ← (( do (ELUsingAArch32 ELd) ) : SailM Bool )
                     (pure (((! w__15) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
                    (pure ((((_get_MDSCR_EL1_Type_SS w__16) == 1#1) : Bool))))
                else (pure false)) && ((! enabled_at_source) : Bool)))) && (enabled_at_dest : Bool)))
    ) : SailM Bool )
  if (w__19 : Bool)
  then
    (do
      ArmFull.assert (21 <b (Sail.BitVec.length spsr)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8525.34-8525.35"
      let SS_bit : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 21)]))
      (pure (SS_bit)))
  else (pure (0#1))


def SCTLR_read__1 (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  (SCTLR_read w__0)


/-- Type quantifiers: k_N : Nat, 26 < k_N -/
def RestoredITBits (spsr : (BitVec k_N)) : SailM (BitVec 8) := do
  let it : (BitVec 8) :=
    ((Sail.BitVec.extractLsb spsr 15 10) +++ (Sail.BitVec.extractLsb spsr 26 25))
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.IL == 1#1) : Bool)
  then
    (do
      let w__1 ← (( do (ConstrainUnpredictableBool Unpredictable_ILZEROIT) ) : SailM Bool )
      let w__2 : (BitVec 8) :=
        if (w__1 : Bool)
        then 0b00000000#8
        else it
      (pure (w__2)))
  else
    (do
      if (((! (IsZero (Sail.BitVec.extractLsb it 7 4))) && (IsZero (Sail.BitVec.extractLsb it 3 0))) : Bool)
      then (pure (0b00000000#8))
      else
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          let itd ← (( do
            if ((w__3.EL == EL2) : Bool)
            then
              (do
                let w__4 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
                (pure ((_get_HSCTLR_Type_ITD w__4))))
            else
              (do
                let w__5 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                (pure ((_get_SCTLR_Type_ITD w__5)))) ) : SailM (BitVec 1) )
          (pure (if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 5)])) == 0#1) && (! (IsZero
                       it))) || ((itd == 1#1) && (! (IsZero (Sail.BitVec.extractLsb it 2 0))))) : Bool)
            then 0b00000000#8
            else it))))


end ArmFull.Functions
