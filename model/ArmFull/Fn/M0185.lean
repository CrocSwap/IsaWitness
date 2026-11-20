module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0178
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

def AArch64_IsUnprivAccessPriv (_ : Unit) : SailM Bool := do
  let privileged ← (( do (undefined_bool_at (← occLabel 1676) ()) ) : SailM Bool )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__0.EL
  let privileged ← (( do
    if ((questionMark == EL0) : Bool)
    then (pure (false))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     (HaveNVExt ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV w__4) +++ (_get_HCR_EL2_Type_NV1 w__5)) == 0b11#2) : Bool))))
            else (pure false))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__10 ← (( do
                  if ((← do
                       (HaveVirtHostExt ())) : Bool)
                  then
                    (do
                      let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                  else (pure false) ) : SailM Bool )
                let privileged := ((! w__10) : Bool)
                (pure (privileged)))
            else
              (let privileged : Bool :=
                if ((questionMark == EL3) : Bool)
                then true
                else privileged
              (pure (privileged))))) ) : SailM Bool )
  let w__13 ← (( do
    if ((← do
         (HaveUAOExt ())) : Bool)
    then
      (do
        let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__12.UAO == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      let privileged := ((w__14.EL != EL0) : Bool)
      (pure (privileged)))
  else (pure (privileged))


def IsTMEEnabled (_ : Unit) : SailM Bool := SailME.run do
  let w__6 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailME Bool ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                  (pure (((w__1.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                 (pure (((w__2.EL == EL2) : Bool)))))) : Bool)
    then
      (do
        (HaveEL EL3))
    else (pure false) ) : SailME Bool Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do readReg SCR_EL3 ) : SailME Bool (BitVec 64) )
      if (((_get_SCR_EL3_Type_TME w__7) == 0#1) : Bool)
      then
        (do
          SailME.throw (false : Bool))
      else (pure (())))
  else (pure (()))
  let w__12 ← (( do
    if ((← do
         if ((← do
              let w__8 ← (( do readReg PSTATE ) : SailME Bool ProcState )
              (pure (((w__8.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__9 ← (( do readReg PSTATE ) : SailME Bool ProcState )
             (pure (((w__9.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailME Bool Bool )
  if (w__12 : Bool)
  then
    (do
      let w__13 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
      if (((_get_HCR_EL2_Type_TME w__13) == 0#1) : Bool)
      then
        (do
          SailME.throw (false : Bool))
      else (pure (())))
  else (pure (()))
  (pure (true))


def EffectiveMDSELR_EL1_BANK (_ : Unit) : SailM (BitVec 2) := do
  let num_bp ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  let num_wp ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
  if (((num_bp ≤b 16) && (num_wp ≤b 16)) : Bool)
  then (pure (0b00#2))
  else
    (do
      let w__12 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       (HaveEL EL3)) : Bool)
                  then
                    (do
                      let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_MDCR_EL3_Type_EBWE w__1) == 0#1) : Bool))))
                  else (pure false)) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      if ((← do
                           let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__3.EL != EL3) : Bool)))) : Bool)
                      then
                        (do
                          (EL2Enabled ()))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                     (pure ((((_get_MDCR_EL2_Type_EBWE w__6) == 0#1) : Bool))))
                 else (pure false))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__9.EL == EL1) : Bool)))) : Bool)
            then
              (do
                let w__10 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
                (pure ((((_get_MDSCR_EL1_Type_EMBWE w__10) == 0#1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__12 : Bool)
      then (pure (0b00#2))
      else
        (do
          let w__13 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
          let bank : (BitVec 2) := (_get_MDSELR_EL1_Type_BANK w__13)
          if (((((bank == 0b11#2) && (num_bp ≤b 48)) && (num_wp ≤b 48)) || (((bank == 0b10#2) && (num_bp ≤b 32)) && (num_wp ≤b 32))) : Bool)
          then
            (do
              let maximum : Int :=
                if ((num_bp >b num_wp) : Bool)
                then num_bp
                else num_wp
              let last_bank : Int := (Int.ediv (Sail.Int.toNatChecked ((maximum -i 1))) 16)
              let selected ← (( do
                ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 2421) 0
                  last_bank))) ) : SailM Nat )
              let __tup_1 : (BitVec 2) := (integer_subrange selected 1 0)
              (pure (__tup_1)))
          else (pure (bank))))


/-- Type quantifiers: k_is_ATS1Ex : Bool -/
def AArch64_isPARFormatD128 (regime : Regime) (is_ATS1Ex : Bool) : SailM Bool := do
  let isPARFormatD128 ← (( do (undefined_bool_at (← occLabel 2638) ()) ) : SailM Bool )
  let w__1 ← (( do
    if (((BEq.beq regime Regime_EL2) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
        (pure (((! w__0) : Bool)))) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      let isPARFormatD128 : Bool := false
      match regime with
      | .Regime_EL3 =>
        (do
          let w__2 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
          let isPARFormatD128 := (((_get_TCR_EL3_Type_D128 w__2) == 1#1) : Bool)
          (pure (isPARFormatD128)))
      | .Regime_EL20 =>
        (do
          let w__3 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
          let isPARFormatD128 := (((_get_TCR2_EL2_Type_D128 w__3) == 1#1) : Bool)
          (pure (isPARFormatD128)))
      | .Regime_EL10 =>
        (do
          let w__8 ← (( do
            if ((← do
                 if ((is_ATS1Ex : Bool) : Bool)
                 then (pure true)
                 else
                   (do
                     let w__4 ← (( do (EL2Enabled ()) ) : SailM Bool )
                     (pure (((! w__4) : Bool))))) : Bool)
            then (pure true)
            else
              (do
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_VM w__6) +++ (_get_HCR_EL2_Type_DC w__7)) == 0b00#2) : Bool))))
            ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              let w__9 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              let isPARFormatD128 := (((_get_TCR2_EL1_Type_D128 w__9) == 1#1) : Bool)
              (pure (isPARFormatD128)))
          else
            (do
              let w__10 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
              let isPARFormatD128 := (((_get_VTCR_EL2_Type_D128 w__10) == 1#1) : Bool)
              (pure (isPARFormatD128))))
      | _ => (pure (isPARFormatD128)))


/-- Type quantifiers: idx : Nat, increment_name : Int, 0 ≤ idx ∧ idx < 31 -/
def AArch32_IncrementEventCounter (idx : Nat) (increment_name : Int) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (0 ≤b idx) "sail-inputs/03-v8_base.sail:43492.36-43492.37"
      ArmFull.assert (idx <b 31) "sail-inputs/03-v8_base.sail:43493.36-43493.37"
      (AArch64_IncrementEventCounter idx increment_name))
  else
    (do
      let w__1 ← (( do (PMEVCNTR_read idx) ) : SailM (BitVec 32) )
      let old_value : Int := (BitVec.toNat w__1)
      let w__2 ← (( do (PMUCountValue idx increment_name) ) : SailM Int )
      let new_value : Int := (old_value +i w__2)
      (PMEVCNTR_set idx (integer_subrange new_value 31 0))
      let ovflw : Nat := 32
      if (((Sail.BitVec.castWidth (m := (64 - (Sail.Int.toNatChecked ovflw) + 1)) (integer_subrange
             old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
      then
        (do
          let w__3 ← (( do (PMOVSSET_read ()) ) : SailM (BitVec 32) )
          (PMOVSSET_write
            (Mk_PMOVSSET_Type (Sail.BitVec.updateSubrange w__3 idx idx (Sail.BitVec.castWidth 1#1))))
          let w__4 ← (( do (PMOVSR_read ()) ) : SailM (BitVec 32) )
          (PMOVSR_write
            (Mk_PMOVSR_Type (Sail.BitVec.updateSubrange w__4 idx idx (Sail.BitVec.castWidth 1#1))))
          let w__6 ← (( do
            if ((((BitVec.setWidth 1 (BitVec.join1 [(integer_access idx 0)])) == 0#1) : Bool) : Bool)
            then
              (do
                let w__5 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                (pure ((((idx +i 1) <b w__5) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (PMUEvent__2 PMU_EVENT_CHAIN 1 (idx +i 1)))
          else (pure (())))
      else (pure (())))


def __get_ID_AA64ISAR0_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : ID_AA64ISAR0_EL1_Type := value_name
  let tmp : ID_AA64ISAR0_EL1_Type :=
    (Mk_ID_AA64ISAR0_EL1_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
          (Sail.BitVec.zeroExtend 0xF#4 64)))))
  let w__10 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__0.EL == EL2) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__1.EL == EL1) : Bool))))) : Bool)
         then
           (do
             let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
             (pure ((((_get_SCR_EL3_Type_TME w__3) == 0#1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             if ((← do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__5.EL == EL1) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TME w__8) == 0#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__10 : Bool)
    then
      (Mk_ID_AA64ISAR0_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0xF000000#28 64)))))
    else tmp
  (pure (tmp))


/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int -/
def AArch64_CheckNVCondsIfCurrentEL (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) : SailM Bool := do
  let is_reg_current_el : Bool :=
    (((((op0 == 3) && (op1 == 0)) && (crn == 4)) && (crm == 2)) && (op2 == 2))
  let have_nv_trap_conds ← (( do
    if ((← do
         if ((← do
              if ((← do
                   (HaveNVExt ())) : Bool)
              then
                (do
                  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__1.EL == EL1) : Bool))))
              else (pure false)) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((Sail.BitVec.castWidth (m := 1) (BitVec.slice w__5 42 1)) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  (pure ((is_reg_current_el && have_nv_trap_conds)))


/-- Type quantifiers: t : Int -/
def CurrentEL_SysRegRead_94be544516d41cc8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__0)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__1.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__2.EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (X_set t 64 (((Zeros (n := 60)) +++ 0b10#2) +++ (Zeros (n := 2)))))
          else
            (do
              let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64 (((Zeros (n := 60)) +++ w__5.EL) +++ (Zeros (n := 2))))))
      else
        (do
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__6.EL == EL2) : Bool)
          then
            (do
              let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64 (((Zeros (n := 60)) +++ w__7.EL) +++ (Zeros (n := 2)))))
          else
            (do
              let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__8.EL == EL3) : Bool)
              then
                (do
                  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64 (((Zeros (n := 60)) +++ w__9.EL) +++ (Zeros (n := 2)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VDISR_EL2_SysRegRead_07ff39acd959bbaf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AMO : (BitVec 1) := (_get_HCR_EL2_Type_AMO w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EA : (BitVec 1) := (_get_SCR_EL3_Type_EA w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_AMO == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VDISR_EL2 w__5)))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      if ((← do
                           (HaveEL EL3)) : Bool)
                      then
                        (do
                          let w__7 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__7) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (X_set t 64 (Zeros (n := 64))))
              else
                (do
                  let w__10 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DISR_EL1 w__10)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (HaveEL EL3)) : Bool)
                      then
                        (do
                          let w__12 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__12) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (X_set t 64 (Zeros (n := 64))))
              else
                (do
                  let w__15 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DISR_EL1 w__15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DISR_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VDISR_EL2_SysRegWrite_22757a602e967277 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AMO : (BitVec 1) := (_get_HCR_EL2_Type_AMO w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EA : (BitVec 1) := (_get_SCR_EL3_Type_EA w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_AMO == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg VDISR_EL2 (Mk_VDISR_EL2_Type w__5))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      if ((← do
                           (HaveEL EL3)) : Bool)
                      then
                        (do
                          let w__7 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__7) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then (pure (()))
              else
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DISR_EL1 (Mk_DISR_EL1_Type w__10))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (HaveEL EL3)) : Bool)
                      then
                        (do
                          let w__12 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__12) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then (pure (()))
              else
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DISR_EL1 (Mk_DISR_EL1_Type w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DISR_EL1 (Mk_DISR_EL1_Type w__16))
              else (pure (())))))


def execute_aarch32_instrs_DMB_Op_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let domain ← (( do (undefined_MBReqDomain (← occLabel 3009) ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes (← occLabel 3010) ()) ) : SailM MBReqTypes )
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match option_name with
    | 0b0001 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b0010 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | 0b0011 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
    | 0b0101 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b0110 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | 0b0111 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
    | 0b1001 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b1010 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | 0b1011 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
    | 0b1101 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b1110 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  let types := types
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let domain ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        let domain : MBReqDomain :=
          if (((_get_HCR_Type_BSU w__5) == 0b11#2) : Bool)
          then MBReqDomain_FullSystem
          else domain
        let w__7 ← (( do
          (pure ((← do
                let w__6 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_BSU w__6) == 0b10#2) : Bool)))) && ((bne domain
                MBReqDomain_FullSystem) : Bool))) ) : SailM Bool )
        let domain : MBReqDomain :=
          if (w__7 : Bool)
          then MBReqDomain_OuterShareable
          else domain
        let w__9 ← (( do
          (pure ((← do
                let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_BSU w__8) == 0b01#2) : Bool)))) && ((BEq.beq domain
                MBReqDomain_Nonshareable) : Bool))) ) : SailM Bool )
        let domain : MBReqDomain :=
          if (w__9 : Bool)
          then MBReqDomain_InnerShareable
          else domain
        (pure (domain)))
    else (pure (domain)) ) : SailM MBReqDomain )
  (DataMemoryBarrier domain types)


end ArmFull.Functions
