import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0044
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0144
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0195
import ArmFull.Fn.M0200
import ArmFull.Fn.M0202

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

/-- Type quantifiers: k_write_spsr : Bool -/
def execute_aarch32_instrs_MSR_i_Op_AS_txt (imm32 : (BitVec 32)) (mask : (BitVec 4)) (write_spsr : Bool) : SailM Unit := do
  if (write_spsr : Bool)
  then
    (do
      let w__2 ← (( do
        if ((← do
             let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__0.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__1.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          (SPSRWriteByInstr imm32 mask)))
  else
    (do
      (CPSRWriteByInstr imm32 mask))


/-- Type quantifiers: increment_name : Int -/
def PMUEvent__1 (pmuevent : (BitVec 16)) (increment_name : Int) : SailM Unit := do
  let w__0 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (SPEEvent pmuevent))
  else (pure (()))
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
         (pure ((((_get_PMCR_EL0_Type_E w__1) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_MDCR_EL2_Type_HPME w__2) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then (pure (()))
  else
    (do
      let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do (PMUEvent__2 pmuevent increment_name idx)
            (pure loop_vars)))
      else (pure (()))
      let w__7 ← (( do
        (pure ((← do
              if ((← do
                   (HaveAArch64 ())) : Bool)
              then
                (do
                  (HavePMUv3ICNTR ()))
              else (pure false)) && ((pmuevent == PMU_EVENT_INST_RETIRED) : Bool))) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          (IncrementInstructionCounter increment_name))
      else (pure (())))


def AArch64_BranchAddr (vaddress : (BitVec 64)) (el : (BitVec 2)) : SailM (BitVec 64) := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  ArmFull.assert (! w__0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6150.35-6150.36"
  let msbit ← (( do (AddrTop vaddress true el) ) : SailM Int )
  if ((msbit == 63) : Bool)
  then (pure (vaddress))
  else
    (do
      ArmFull.assert ((0 ≤b msbit) && (msbit <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6155.54-6155.55"
      let w__3 ← (( do
        (pure ((← do
              if ((((el == EL0) || (el == EL1)) : Bool) : Bool)
              then (pure true)
              else
                (do
                  (IsInHost ()))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access vaddress
                  (Sail.Int.toNatChecked (msbit)))])) == 1#1) : Bool))) ) : SailM Bool )
      let w__4 : (BitVec 64) :=
        if (w__3 : Bool)
        then (sign_extend (Sail.BitVec.extractLsb vaddress (Sail.Int.toNatChecked (msbit)) 0) 64)
        else
          (Sail.BitVec.zeroExtend
            (Sail.BitVec.extractLsb vaddress (Sail.Int.toNatChecked (msbit)) 0) 64)
      (pure (w__4)))


def PC_read__1 (_ : Unit) : SailM (BitVec 32) := do
  (R_read 15)


/-- Type quantifiers: k_N : Nat, k_conditional : Bool, k_taken_flag : Bool, k_N ≥ 0 -/
def SPEBranch (target : (BitVec k_N)) (branch_type : BranchType) (conditional : Bool) (taken_flag : Bool) : SailM Unit := do
  let is_isb : Bool := false
  (SPEBranch__1 target branch_type conditional taken_flag is_isb)


/-- Type quantifiers: width : Nat, width ≥ 0 -/
def FFR_set (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert (width == (Int.ediv (Sail.Int.toNatChecked (VL)) 8)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7006.30-7006.31"
  let w__0 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      writeReg _FFR (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.zeroExtend value_name MAX_PL)))
  else
    (do
      let w__1 ← (( do readReg _FFR ) : SailM (BitVec 256) )
      writeReg _FFR (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.updateSubrange w__1
        (Sail.Int.toNatChecked ((width -i 1))) 0 (Sail.BitVec.castWidth value_name))))


def IsFPEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (ELUsingAArch32 el) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch32_IsFPEnabled el))
  else
    (do
      (AArch64_IsFPEnabled el))


/-- Type quantifiers: n : Int, width : Nat, width ≥ 0 -/
def P_set (n : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7362.27-7362.28"
  ArmFull.assert (width == (Int.ediv (Sail.Int.toNatChecked (VL)) 8)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7363.30-7363.31"
  let w__0 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 16)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7365.46-7365.47"
      let w__1 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
      writeReg _P (vectorUpdate w__1 (Sail.Int.toNatChecked (n))
        (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.zeroExtend value_name MAX_PL))))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 16)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7368.46-7368.47"
      let w__2 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
      let w__3 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
      writeReg _P (vectorUpdate w__2 (Sail.Int.toNatChecked (n))
        (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.updateSubrange
          (GetElem?.getElem! w__3 (Sail.Int.toNatChecked (n)))
          (Sail.Int.toNatChecked ((width -i 1))) 0 (Sail.BitVec.castWidth value_name)))))


/-- Type quantifiers: n : Int, width : Nat, List.elem width [8, 16, 32, 64, 128] -/
def V_set (n : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7420.27-7420.28"
  ArmFull.assert ((width == 8) || ((width == 16) || ((width == 32) || ((width == 64) || (width == 128))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7421.78-7421.79"
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsSVEEnabled w__0.EL) ) : SailM Bool )
  let vlen : Int :=
    if (w__1 : Bool)
    then VL
    else 128
  let w__2 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
      writeReg _Z (vectorUpdate w__3 (Sail.Int.toNatChecked (n))
        (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.zeroExtend value_name MAX_VL))))
  else
    (do
      let w__4 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
      let w__5 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
      writeReg _Z (vectorUpdate w__4 (Sail.Int.toNatChecked (n))
        (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.updateSubrange
          (GetElem?.getElem! w__5 (Sail.Int.toNatChecked (n))) (Sail.Int.toNatChecked ((vlen -i 1)))
          0
          (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend value_name (Sail.Int.toNatChecked (vlen))))))))


/-- Type quantifiers: n : Int, width : Nat, width ≥ 0 -/
def Z_set (n : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7448.27-7448.28"
  ArmFull.assert (width == VL) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7449.22-7449.23"
  let w__0 ← (( do (ConstrainUnpredictableBool Unpredictable_SVEZEROUPPER) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
      writeReg _Z (vectorUpdate w__1 (Sail.Int.toNatChecked (n))
        (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.zeroExtend value_name MAX_VL))))
  else
    (do
      let w__2 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
      let w__3 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
      writeReg _Z (vectorUpdate w__2 (Sail.Int.toNatChecked (n))
        (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.updateSubrange
          (GetElem?.getElem! w__3 (Sail.Int.toNatChecked (n)))
          (Sail.Int.toNatChecked ((width -i 1))) 0 (Sail.BitVec.castWidth value_name)))))


/-- Type quantifiers: k_N : Nat, k_illegal_psr_state : Bool, 31 < k_N -/
def SetPSTATEFromPSR__1 (spsr_in : (BitVec k_N)) (illegal_psr_state : Bool) : SailM Unit := do
  let spsr : (BitVec k_N) := spsr_in
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  let from_aarch64 : Bool := (! w__0)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (DebugExceptionReturnSS spsr) ) : SailM (BitVec 1) )
  writeReg PSTATE { w__1 with SS := w__2 }
  writeReg ShouldAdvanceSS false
  if (illegal_psr_state : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with IL := 1#1 }
      let w__4 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__6 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
          writeReg PSTATE { w__5 with SSBS := w__6 })
      else (pure (()))
      let w__7 ← (( do (HaveBTIExt ()) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__9 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
          writeReg PSTATE { w__8 with BTYPE := w__9 })
      else (pure (()))
      let w__10 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__12 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
          writeReg PSTATE { w__11 with UAO := w__12 })
      else (pure (()))
      let w__13 ← (( do (HaveDITExt ()) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__15 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
          writeReg PSTATE { w__14 with DIT := w__15 })
      else (pure (()))
      let w__16 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if (w__16 : Bool)
      then
        (do
          let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__18 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
          writeReg PSTATE { w__17 with TCO := w__18 })
      else (pure (())))
  else
    (do
      ArmFull.assert (20 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8854.34-8854.35"
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with IL := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 20)])) }
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 4)])) == 1#1) : Bool)
      then
        (do
          (AArch32_WriteMode (Sail.BitVec.extractLsb spsr 4 0))
          let w__20 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
          if (w__20 : Bool)
          then
            (do
              ArmFull.assert (23 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8859.42-8859.43"
              let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__21 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    spsr 23)])) })
          else (pure (())))
      else
        (do
          let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__22 with nRW := 0#1 }
          let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__23 with EL := (Sail.BitVec.extractLsb spsr 3 2) }
          let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__24 with SP := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 0)])) }
          let w__25 ← (( do (HaveBTIExt ()) ) : SailM Bool )
          if (w__25 : Bool)
          then
            (do
              let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__26 with BTYPE := (Sail.BitVec.extractLsb spsr 11 10) })
          else (pure (()))
          let w__27 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
          if (w__27 : Bool)
          then
            (do
              let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__28 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    spsr 12)])) })
          else (pure (()))
          let w__29 ← (( do (HaveUAOExt ()) ) : SailM Bool )
          if (w__29 : Bool)
          then
            (do
              ArmFull.assert (23 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8874.42-8874.43"
              let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__30 with UAO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    spsr 23)])) })
          else (pure (()))
          let w__31 ← (( do (HaveDITExt ()) ) : SailM Bool )
          if (w__31 : Bool)
          then
            (do
              ArmFull.assert (24 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8878.42-8878.43"
              let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__32 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    spsr 24)])) })
          else (pure (()))
          let w__33 ← (( do (HaveMTEExt ()) ) : SailM Bool )
          if (w__33 : Bool)
          then
            (do
              ArmFull.assert (25 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8882.42-8882.43"
              let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__34 with TCO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    spsr 25)])) })
          else (pure (()))
          let w__35 ← (( do (HaveGCS ()) ) : SailM Bool )
          if (w__35 : Bool)
          then
            (do
              ArmFull.assert (34 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8886.42-8886.43"
              let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__36 with EXLOCK := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    spsr 34)])) })
          else (pure (()))))
  let w__39 ← (( do
    if ((← do
         let w__37 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__37.IL == 1#1) : Bool)))) : Bool)
    then
      (do
        let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__38.nRW == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let spsr ← (( do
    if (w__39 : Bool)
    then
      (do
        let w__40 ← (( do (ConstrainUnpredictableBool Unpredictable_ILZEROT) ) : SailM Bool )
        if (w__40 : Bool)
        then
          (do
            ArmFull.assert (5 <b (Sail.BitVec.length spsr_in)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8894.37-8894.38"
            let spsr : (BitVec k_N) := (BitVec.update spsr 5 (Bit 0#1))
            (pure (spsr)))
        else (pure (spsr)))
    else (pure (spsr)) ) : SailM (BitVec k_N) )
  let split_vec := (Sail.BitVec.extractLsb spsr 31 28)
  let w__41 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__41 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__42 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__43 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__43 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__44 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__45 ← (( do (HavePANExt ()) ) : SailM Bool )
  if (w__45 : Bool)
  then
    (do
      let w__46 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__46 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 22)])) })
  else (pure (()))
  let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__47.nRW == 1#1) : Bool)
  then
    (do
      let w__48 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__48 with Q := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 27)])) }
      let w__49 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__50 ← (( do (RestoredITBits spsr) ) : SailM (BitVec 8) )
      writeReg PSTATE { w__49 with IT := w__50 }
      writeReg ShouldAdvanceIT false
      let w__51 ← (( do (HaveDITExt ()) ) : SailM Bool )
      if (w__51 : Bool)
      then
        (do
          let w__52 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__54 ← (( do
            (pure ((← do
                  (Restarting ())) || from_aarch64)) ) : SailM Bool )
          let w__55 : (BitVec 1) :=
            if (w__54 : Bool)
            then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 24)]))
            else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 21)]))
          writeReg PSTATE { w__52 with DIT := w__55 })
      else (pure (()))
      let w__56 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__56 with GE := (Sail.BitVec.extractLsb spsr 19 16) }
      let w__57 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__57 with E := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 9)])) }
      let split_vec := (Sail.BitVec.extractLsb spsr 8 6)
      let w__58 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__58 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__59 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__59 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__60 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__60 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      let w__61 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__61 with T := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 5)])) })
  else
    (do
      let w__62 ← (( do (HaveFeatNMI ()) ) : SailM Bool )
      if (w__62 : Bool)
      then
        (do
          let w__63 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__63 with ALLINT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                spsr 13)])) })
      else (pure (()))
      let split_vec := (Sail.BitVec.extractLsb spsr 9 6)
      let w__64 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__64 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__65 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__65 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__66 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__66 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__67 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__67 with F := (Sail.BitVec.extractLsb split_vec 0 0) })


def AArch64_PendingUnmaskedPhysicalInterrupts (mask_in : (BitVec 3)) : SailM (Bool × Bool × Bool) := do
  let fiq ← (( do (undefined_bool_at (← occLabel 707) ()) ) : SailM Bool )
  let fiq_nmi ← (( do (undefined_bool_at (← occLabel 708) ()) ) : SailM Bool )
  let irq ← (( do (undefined_bool_at (← occLabel 709) ()) ) : SailM Bool )
  let irq_nmi ← (( do (undefined_bool_at (← occLabel 710) ()) ) : SailM Bool )
  let mask : (BitVec 3) := mask_in
  let se_pending : (BitVec 1) :=
    if ((IsPhysicalSErrorPending ()) : Bool)
    then 1#1
    else 0#1
  let w__0 ← (( do (IRQPending ()) ) : SailM (Bool × Bool) )
  let (tup__0, tup__1) := (w__0 : (Bool × Bool))
  let irq : Bool := tup__0
  let irq_nmi : Bool := tup__1
  let (tup__0, tup__1) := ((FIQPending ()) : (Bool × Bool))
  let fiq : Bool := tup__0
  let fiq_nmi : Bool := tup__1
  let irq_pending : (BitVec 1) :=
    if (irq : Bool)
    then 1#1
    else 0#1
  let fiq_pending : (BitVec 1) :=
    if (fiq : Bool)
    then 1#1
    else 0#1
  let allintmask ← (( do (undefined_bitvector_at (← occLabel 711) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do
    if ((← do
         (HaveFeatNMI ())) : Bool)
    then
      (do
        let w__2 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLRType_NMI w__2) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let (allintmask, mask) ← (( do
    if (w__3 : Bool)
    then
      (do
        let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        let w__6 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        let allintmask :=
          ((w__4.ALLINT ||| (w__5.SP &&& (_get_SCTLRType_SPINTMASK w__6))) : (BitVec 1))
        let w__8 ← (( do
          (pure ((← do
                let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__7.EL == EL0) : Bool)))) || ((allintmask == 0#1) : Bool))) ) : SailM Bool
          )
        let mask : (BitVec 3) :=
          if (w__8 : Bool)
          then
            (let mask : (BitVec 3) :=
              if (irq_nmi : Bool)
              then (BitVec.update mask 1 (Bit 0#1))
              else mask
            if (fiq_nmi : Bool)
            then (BitVec.update mask 0 (Bit 0#1))
            else mask)
          else mask
        (pure ((allintmask, mask))))
    else
      (let allintmask : (BitVec 1) := 0#1
      (pure ((allintmask, mask)))) ) : SailM ((BitVec 1) × (BitVec 3)) )
  let pending : (BitVec 3) := ((se_pending +++ irq_pending) +++ fiq_pending)
  let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
  let mask ← (( do
    if (w__9 : Bool)
    then
      (do
        let mask_override ← (( do (undefined_bitvector_at (← occLabel 712) 3) ) : SailM
          (BitVec 3) )
        let w__14 ← (( do
          if ((← do
               if ((← do
                    (HaveVirtHostExt ())) : Bool)
               then
                 (do
                   let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_E2H w__11) == 1#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_TGE w__13) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let mask_override ← (( do
          if (w__14 : Bool)
          then (pure (0b000#3))
          else
            (do
              let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if (((_get_HCR_EL2_Type_TGE w__15) == 1#1) : Bool)
              then (pure (0b111#3))
              else
                (do
                  let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let mask_override :=
                    (((_get_HCR_EL2_Type_AMO w__16) +++ ((_get_HCR_EL2_Type_IMO w__17) +++ (_get_HCR_EL2_Type_FMO
                          w__18))) : (BitVec 3))
                  (pure (mask_override)))) ) : SailM (BitVec 3) )
        let w__21 ← (( do
          if ((← do
               let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__19.EL == EL0) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__20.EL == EL1) : Bool)))) ) : SailM Bool )
        if (w__21 : Bool)
        then
          (let mask : (BitVec 3) := (mask &&& (Complement.complement mask_override))
          (pure (mask)))
        else
          (do
            let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
            if ((w__22.EL == EL2) : Bool)
            then
              (do
                let w__25 ← (( do
                  if ((← do
                       let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                       (pure (((! w__23) : Bool)))) : Bool)
                  then
                    (do
                      let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_TGE w__24) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let mask : (BitVec 3) :=
                  if (w__25 : Bool)
                  then (mask ||| (Complement.complement mask_override))
                  else mask
                (pure (mask)))
            else (pure (mask))))
    else (pure (mask)) ) : SailM (BitVec 3) )
  let mask ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__26.EL != EL3) : Bool)
        then
          (do
            let w__27 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__28 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__29 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let mask :=
              ((mask &&& (Complement.complement
                  ((_get_SCR_EL3_Type_EA w__27) +++ ((_get_SCR_EL3_Type_IRQ w__28) +++ (_get_SCR_EL3_Type_FIQ
                        w__29))))) : (BitVec 3))
            (pure (mask)))
        else
          (do
            let w__30 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__31 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__32 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let mask :=
              ((mask ||| (Complement.complement
                  ((_get_SCR_EL3_Type_EA w__30) +++ ((_get_SCR_EL3_Type_IRQ w__31) +++ (_get_SCR_EL3_Type_FIQ
                        w__32))))) : (BitVec 3))
            (pure (mask))))
    else (pure (mask)) ) : SailM (BitVec 3) )
  let w__34 ← (( do
    (pure ((← do
          let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__33.EL != EL0) : Bool)))) && ((allintmask == 1#1) : Bool))) ) : SailM Bool )
  let mask ← (( do
    if (w__34 : Bool)
    then
      (do
        let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__35.EL == EL1) : Bool)
        then
          (do
            let w__38 ← (( do
              if ((← do
                   let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_FMO w__36) == 0#1) : Bool)))) : Bool)
              then
                (do
                  let w__37 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_FIQ w__37) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let mask : (BitVec 3) :=
              if (w__38 : Bool)
              then (BitVec.update mask 0 (Bit 1#1))
              else mask
            let w__41 ← (( do
              if ((← do
                   let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_IMO w__39) == 0#1) : Bool)))) : Bool)
              then
                (do
                  let w__40 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_IRQ w__40) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let mask : (BitVec 3) :=
              if (w__41 : Bool)
              then (BitVec.update mask 1 (Bit 1#1))
              else mask
            (pure (mask)))
        else
          (do
            let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
            if ((w__42.EL == EL2) : Bool)
            then
              (do
                let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let mask : (BitVec 3) :=
                  if (((_get_HCR_EL2_Type_FMO w__43) == 1#1) : Bool)
                  then (BitVec.update mask 0 (Bit 1#1))
                  else mask
                let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let mask : (BitVec 3) :=
                  if (((_get_HCR_EL2_Type_IMO w__44) == 1#1) : Bool)
                  then (BitVec.update mask 1 (Bit 1#1))
                  else mask
                (pure (mask)))
            else
              (do
                let w__45 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let mask : (BitVec 3) :=
                  if (((_get_SCR_EL3_Type_FIQ w__45) == 1#1) : Bool)
                  then (BitVec.update mask 0 (Bit 1#1))
                  else mask
                let w__46 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let mask : (BitVec 3) :=
                  if (((_get_SCR_EL3_Type_IRQ w__46) == 1#1) : Bool)
                  then (BitVec.update mask 1 (Bit 1#1))
                  else mask
                (pure (mask)))))
    else (pure (mask)) ) : SailM (BitVec 3) )
  let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access unmasked_pending 2)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          unmasked_pending 1)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          unmasked_pending 0)])) == 1#1))))


end ArmFull.Functions
