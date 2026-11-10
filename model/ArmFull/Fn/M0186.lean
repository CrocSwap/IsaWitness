import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0052
import ArmFull.Fn.M0070
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183

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

/-- Type quantifiers: idx : Nat, increment_name : Int, 0 ≤ idx ∧ idx < 31 -/
def AArch64_IncrementEventCounter (idx : Nat) (increment_name : Int) : SailM Unit := do
  let ovflw : Int := 32
  let w__0 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let old_value : Int := (BitVec.toNat (GetElem?.getElem! w__0 idx))
  let w__1 ← (( do (PMUCountValue idx increment_name) ) : SailM Int )
  let new_value : Int := (old_value +i w__1)
  let lp ← (( do (undefined_bitvector_at (← occLabel 2422) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
  let (lp, ovflw) ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
        writeReg PMEVCNTR_EL0 (vectorUpdate w__3 idx (integer_subrange new_value 63 0))
        let w__4 ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
        let w__7 ← (( do
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HLP w__5))))
          else
            (do
              let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
              (pure ((_get_PMCR_EL0_Type_LP w__6)))) ) : SailM (BitVec 1) )
        let lp := (w__7 : (BitVec 1))
        let ovflw : Int :=
          if ((lp == 1#1) : Bool)
          then 64
          else 32
        (pure ((lp, ovflw))))
    else
      (do
        let w__8 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
        writeReg PMEVCNTR_EL0 (vectorUpdate w__8 idx
          (Sail.BitVec.zeroExtend (integer_subrange new_value 31 0) 64))
        let ovflw : Int := 32
        (pure ((lp, ovflw)))) ) : SailM ((BitVec 1) × Int) )
  let ovflw : Int := ovflw
  if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
         old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
  then
    (do
      let w__9 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSSET_EL0 (BitVec.update w__9 idx (Bit 1#1))
      let w__10 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSCLR_EL0 (BitVec.update w__10 idx (Bit 1#1))
      let w__15 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(integer_access idx 0)])) == 0#1) : Bool) : Bool)
             then
               (do
                 let w__11 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                 (pure ((((idx +i 1) <b w__11) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (pure ((← do
                  let w__13 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
                  (pure (((! w__13) : Bool)))) || ((lp == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (PMUEvent__2 PMU_EVENT_CHAIN 1 (idx +i 1)))
      else (pure (())))
  else (pure (()))


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


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV94 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap4_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV93 enabled)
      (__ConfigureV89 enabled))
  else (pure (()))


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
              let w__8 ← (( do
                (pure ((← do
                      if (((HaveEL EL3) : Bool) : Bool)
                      then
                        (do
                          let w__6 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__6) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (X_set t 64 (Zeros (n := 64))))
              else
                (do
                  let w__9 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DISR_EL1 w__9)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      if (((HaveEL EL3) : Bool) : Bool)
                      then
                        (do
                          let w__10 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__10) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (X_set t 64 (Zeros (n := 64))))
              else
                (do
                  let w__13 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DISR_EL1 w__13))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__14 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DISR_EL1 w__14)))
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
              let w__8 ← (( do
                (pure ((← do
                      if (((HaveEL EL3) : Bool) : Bool)
                      then
                        (do
                          let w__6 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__6) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then (pure (()))
              else
                (do
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DISR_EL1 (Mk_DISR_EL1_Type w__9))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      if (((HaveEL EL3) : Bool) : Bool)
                      then
                        (do
                          let w__10 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__10) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then (pure (()))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DISR_EL1 (Mk_DISR_EL1_Type w__13)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DISR_EL1 (Mk_DISR_EL1_Type w__14))
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


def PMUCounterMask (_ : Unit) : SailM (BitVec 64) := do
  let n ← (( do (undefined_int_at (← occLabel 502) ()) ) : SailM Int )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  let n ← (( do
    if (w__0 : Bool)
    then
      (do
        (AArch32_GetNumEventCountersAccessible ()))
    else
      (do
        (AArch64_GetNumEventCountersAccessible ())) ) : SailM Int )
  let n : Int := n
  ArmFull.assert (n ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4047.30-4047.31"
  ArmFull.assert (64 ≥b n) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4048.31-4048.32"
  let mask : (BitVec 64) := (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (n)))) 64)
  let mask : (BitVec 64) := (BitVec.update mask CYCLE_COUNTER_ID (Bit 1#1))
  let w__5 ← (( do
    if ((← do
         (HaveAArch64 ())) : Bool)
    then
      (do
        (HavePMUv3ICNTR ()))
    else (pure false) ) : SailM Bool )
  let mask : (BitVec 64) :=
    if (w__5 : Bool)
    then (BitVec.update mask INSTRUCTION_COUNTER_ID (Bit 1#1))
    else mask
  (pure (mask))


def CurrentSecurityState (_ : Unit) : SailM SecurityState := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (SecurityStateAtEL w__0.EL)


/-- Type quantifiers: k_resvd_for_el2 : Bool -/
def HiLoPMUOverflow (resvd_for_el2 : Bool) : SailM Bool := do
  let check_cnten : Bool := false
  let check_e : Bool := false
  let check_inten : Bool := false
  let include_lo_name : Bool := (! resvd_for_el2)
  let include_hi_name : Bool := resvd_for_el2
  let exclude_cyc : Bool := false
  let exclude_sync : Bool := false
  (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc
    exclude_sync)


def S1TranslationRegime (el : (BitVec 2)) : SailM (BitVec 2) := do
  if ((el != EL0) : Bool)
  then (pure (el))
  else
    (do
      let w__3 ← (( do
        if ((← do
             if (((HaveEL EL3) : Bool) : Bool)
             then
               (do
                 (ELUsingAArch32 EL3))
             else (pure false)) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__2) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (EL3))
      else
        (do
          let w__6 ← (( do
            if ((← do
                 (HaveVirtHostExt ())) : Bool)
            then
              (do
                (ELIsInHost el))
            else (pure false) ) : SailM Bool )
          let w__7 : (BitVec 2) :=
            if (w__6 : Bool)
            then EL2
            else EL1
          (pure (w__7))))


def IsInHost (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (ELIsInHost w__0.EL)


def StatisticalProfilingEnabled__1 (el : (BitVec 2)) : SailM Bool := do
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 590) 2) ) : SailM (BitVec 2) )
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 591) ()) ) : SailM SecurityState )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             (UsingAArch32 ()))) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (ProfilingBufferEnabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then (pure (false))
  else
    (do
      let tge_set ← (( do
        if ((← do
             (EL2Enabled ())) : Bool)
        then
          (do
            let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let w__7 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
      let (tup__0, tup__1) := (w__7 : (SecurityState × (BitVec 2)))
      let owning_ss : SecurityState := tup__0
      let owning_el : (BitVec 2) := tup__1
      let w__9 ← (( do
        if ((((BitVec.toNat owning_el) <b (BitVec.toNat el)) || (tge_set && (owning_el == EL1))) : Bool)
        then (pure true)
        else
          (do
            let w__8 ← (( do (SecurityStateAtEL el) ) : SailM SecurityState )
            (pure (((bne owning_ss w__8) : Bool)))) ) : SailM Bool )
      if (w__9 : Bool)
      then (pure (false))
      else
        (do
          let spe_bit ← (( do (undefined_bitvector_at (← occLabel 592) 1) ) : SailM (BitVec 1) )
          let questionMark := el
          let spe_bit ← (( do
            if ((questionMark == EL3) : Bool)
            then
              (do
                (Unreachable ())
                (pure (spe_bit)))
            else
              (do
                if ((questionMark == EL2) : Bool)
                then
                  (do
                    let w__10 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
                    let spe_bit := ((_get_PMSCR_EL2_Type_E2SPE w__10) : (BitVec 1))
                    (pure (spe_bit)))
                else
                  (do
                    if ((questionMark == EL1) : Bool)
                    then
                      (do
                        let w__11 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
                        let spe_bit := ((_get_PMSCR_EL1_Type_E1SPE w__11) : (BitVec 1))
                        (pure (spe_bit)))
                    else
                      (do
                        if ((questionMark == EL0) : Bool)
                        then
                          (do
                            if (tge_set : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
                                (pure ((_get_PMSCR_EL2_Type_E0HSPE w__12))))
                            else
                              (do
                                let w__13 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
                                (pure ((_get_PMSCR_EL1_Type_E0SPE w__13)))))
                        else (pure (spe_bit))))) ) : SailM (BitVec 1) )
          (pure ((spe_bit == 1#1)))))


end ArmFull.Functions
