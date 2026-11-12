import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0044
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0141
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0173
import ArmFull.Fn.M0185
import ArmFull.Fn.M0237
import ArmFull.Fn.M0253
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0924
import ArmFull.Fn.M1142

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

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4614) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4615)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then
          (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "sail-arm/instrs64.sail:37529.72-37529.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "sail-arm/instrs64.sail:37532.73-37532.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (let address : (BitVec 64) :=
            if (postindex : Bool)
            then (address + offset)
            else address
          (pure (address))) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_unsigned (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4678) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4679)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then
          (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "sail-arm/instrs64.sail:39819.72-39819.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "sail-arm/instrs64.sail:39822.73-39822.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (let address : (BitVec 64) :=
            if (postindex : Bool)
            then (address + offset)
            else address
          (pure (address))) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_set (d : Nat) (n : Nat) (options_name : (BitVec 2)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let setsize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let data ← (( do (X_read s 8) ) : SailM (BitVec 8) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let nzcv : (BitVec 4) := (w__0.N +++ (w__1.Z +++ (w__2.C +++ w__3.V)))
  let stagesetsize ← (( do (undefined_bitvector_at (← occLabel 4767) 64) ) : SailM (BitVec 64) )
  let is_setg : Bool := false
  let B ← (( do (undefined_int_at (← occLabel 4768) ()) ) : SailM Int )
  let supports_option_a ← (( do (SETOptionA ()) ) : SailM Bool )
  let privileged ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 0)])) == 1#1) : Bool)
    then
      (do
        (AArch64_IsUnprivAccessPriv ()))
    else
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((w__5.EL != EL0)))) ) : SailM Bool )
  let nontemporal : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 1)])) == 1#1)
  let accdesc ← (( do (CreateAccDescMOPS MemOp_STORE privileged nontemporal) ) : SailM
    AccessDescriptor )
  let (nzcv, setsize, stagesetsize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let setsize : (BitVec 64) :=
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access setsize 63)])) == 1#1) : Bool)
          then 0x7FFFFFFFFFFFFFFF#64
          else setsize
        let (nzcv, setsize, toaddress) : ((BitVec 4) × (BitVec 64) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let toaddress : (BitVec 64) := (toaddress + setsize)
            let setsize : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Zeros (n := 64))) - setsize)
            (nzcv, setsize, toaddress))
          else
            (let nzcv : (BitVec 4) := 0b0010#4
            (nzcv, setsize, toaddress))
        let w__6 ← (( do (SETPreSizeChoice toaddress setsize is_setg) ) : SailM (BitVec 64) )
        let stagesetsize := (w__6 : (BitVec 64))
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access stagesetsize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                setsize 63)]))) || (stagesetsize == (Sail.BitVec.castWidth (m := 64) (Zeros
              (n := 64))))) "armcert/armcert_c27.sail:739.78-739.79"
        if (((BitVec.toInt setsize) >b 0) : Bool)
        then
          (do
            ArmFull.assert ((BitVec.toInt stagesetsize) ≤b (BitVec.toInt setsize)) "armcert/armcert_c27.sail:741.54-741.55")
        else
          (do
            ArmFull.assert ((BitVec.toInt stagesetsize) ≥b (BitVec.toInt setsize)) "armcert/armcert_c27.sail:743.54-743.55")
        (pure ((nzcv, setsize, stagesetsize, toaddress))))
    else
      (do
        let postsize ← (( do (SETPostSizeChoice toaddress setsize is_setg) ) : SailM (BitVec 64) )
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access postsize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                setsize 63)]))) || (postsize == (Sail.BitVec.castWidth (m := 64) (Zeros (n := 64))))) "armcert/armcert_c27.sail:747.70-747.71"
        let zero_size_exceptions ← (( do (MemSetZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt setsize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)])) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                      options_name is_setg))
                else (pure (())))
            else
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)])) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                      options_name is_setg))
                else (pure (()))))
        else (pure (()))
        let stagesetsize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagesetsize : (BitVec 64) := (setsize - postsize)
              let w__7 ← (( do (MemSetParametersIllformedM toaddress setsize is_setg) ) : SailM
                Bool )
              if (w__7 : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                    options_name is_setg))
              else (pure (()))
              (pure (stagesetsize)))
          else
            (do
              let stagesetsize : (BitVec 64) := postsize
              let w__9 ← (( do
                if (((setsize != postsize) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    (MemSetParametersIllformedE toaddress setsize is_setg)) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                    options_name is_setg))
              else (pure (()))
              (pure (stagesetsize))) ) : SailM (BitVec 64) )
        (pure ((nzcv, setsize, stagesetsize, toaddress)))) ) : SailM
    ((BitVec 4) × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
  let w__10 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      (SPESampleMemSet ()))
  else (pure (()))
  let (setsize, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, setsize, stagesetsize) ← (( do
          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (B, setsize, stagesetsize) => (pure ((BitVec.toInt
                stagesetsize) <b 0))) (B, setsize, stagesetsize)
            fun (B, setsize, stagesetsize) => do
              let w__11 ← (( do
                (SETSizeChoice toaddress setsize 1 (Neg.neg (BitVec.toInt stagesetsize))) ) : SailM
                Int )
              let B : Int := (w__11 : Int)
              ArmFull.assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagesetsize))) "armcert/armcert_c27.sail:790.54-790.55"
              let B : Int := B
              ArmFull.assert ((B *i 8) ≥b 0) "armcert/armcert_c27.sail:793.48-793.49"
              (Mem_set (toaddress + setsize) (Sail.Int.toNatChecked (B)) accdesc
                (Sail.BitVec.castWidth (BitVec.replicateBits data (Sail.Int.toNatChecked (B)))))
              let setsize : (BitVec 64) := (BitVec.addInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.addInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 setsize))
              else (pure (()))
              (pure ((B, setsize, stagesetsize)))
          (pure loop_vars) ) : SailM (Int × (BitVec 64) × (BitVec 64)) )
        (pure ((setsize, toaddress))))
    else
      (do
        let (B, setsize, stagesetsize, toaddress) ← (( do
          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (B, setsize, stagesetsize, toaddress) => (pure ((BitVec.toNat
                stagesetsize) >b 0))) (B, setsize, stagesetsize, toaddress)
            fun (B, setsize, stagesetsize, toaddress) => do
              let w__12 ← (( do (SETSizeChoice toaddress setsize 1 (BitVec.toNat stagesetsize)) )
                : SailM Int )
              let B : Int := (w__12 : Int)
              ArmFull.assert (B ≤b (BitVec.toNat stagesetsize)) "armcert/armcert_c27.sail:806.42-806.43"
              let B : Int := B
              ArmFull.assert ((B *i 8) ≥b 0) "armcert/armcert_c27.sail:809.48-809.49"
              (Mem_set toaddress (Sail.Int.toNatChecked (B)) accdesc
                (Sail.BitVec.castWidth (BitVec.replicateBits data (Sail.Int.toNatChecked (B)))))
              let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
              let setsize : (BitVec 64) := (BitVec.subInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.subInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 setsize)
                  (X_set d 64 toaddress))
              else (pure (()))
              (pure ((B, setsize, stagesetsize, toaddress)))
          (pure loop_vars) ) : SailM (Int × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
        (pure ((setsize, toaddress)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 setsize)
      (X_set d 64 toaddress)
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__13 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__14 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__15 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__16 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_setg (d : Nat) (n : Nat) (options_name : (BitVec 2)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let setsize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let data ← (( do (X_read s 8) ) : SailM (BitVec 8) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let nzcv : (BitVec 4) := (w__0.N +++ (w__1.Z +++ (w__2.C +++ w__3.V)))
  let stagesetsize ← (( do (undefined_bitvector_at (← occLabel 4773) 64) ) : SailM (BitVec 64) )
  let is_setg : Bool := true
  let B ← (( do (undefined_int_at (← occLabel 4774) ()) ) : SailM Int )
  let supports_option_a ← (( do (SETGOptionA ()) ) : SailM Bool )
  let privileged ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 0)])) == 1#1) : Bool)
    then
      (do
        (AArch64_IsUnprivAccessPriv ()))
    else
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((w__5.EL != EL0)))) ) : SailM Bool )
  let nontemporal : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 1)])) == 1#1)
  let accdesc ← (( do (CreateAccDescSTGMOPS privileged nontemporal) ) : SailM AccessDescriptor )
  let (nzcv, setsize, stagesetsize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let setsize : (BitVec 64) :=
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access setsize 63)])) == 1#1) : Bool)
          then 0x7FFFFFFFFFFFFFF0#64
          else setsize
        if (((setsize != (Sail.BitVec.castWidth (m := 64) (Zeros (n := 64)))) && (! (IsAligned__1
                 toaddress TAG_GRANULE))) : Bool)
        then
          (do
            let w__6 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
            (AArch64_Abort toaddress w__6))
        else (pure (()))
        if ((! (IsAligned__1 setsize TAG_GRANULE)) : Bool)
        then
          (do
            let w__7 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
            (AArch64_Abort toaddress w__7))
        else (pure (()))
        let (nzcv, setsize, toaddress) : ((BitVec 4) × (BitVec 64) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let toaddress : (BitVec 64) := (toaddress + setsize)
            let setsize : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Zeros (n := 64))) - setsize)
            (nzcv, setsize, toaddress))
          else
            (let nzcv : (BitVec 4) := 0b0010#4
            (nzcv, setsize, toaddress))
        let w__8 ← (( do (SETPreSizeChoice toaddress setsize is_setg) ) : SailM (BitVec 64) )
        let stagesetsize := (w__8 : (BitVec 64))
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access stagesetsize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                setsize 63)]))) || (stagesetsize == (Sail.BitVec.castWidth (m := 64) (Zeros
              (n := 64))))) "armcert/armcert_c27.sail:868.78-868.79"
        ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb stagesetsize 3 0)) == 0b0000#4) "armcert/armcert_c27.sail:869.45-869.46"
        if (((BitVec.toInt setsize) >b 0) : Bool)
        then
          (do
            ArmFull.assert ((BitVec.toInt stagesetsize) ≤b (BitVec.toInt setsize)) "armcert/armcert_c27.sail:871.54-871.55")
        else
          (do
            ArmFull.assert ((BitVec.toInt stagesetsize) ≥b (BitVec.toInt setsize)) "armcert/armcert_c27.sail:873.54-873.55")
        (pure ((nzcv, setsize, stagesetsize, toaddress))))
    else
      (do
        let postsize ← (( do (SETPostSizeChoice toaddress setsize is_setg) ) : SailM (BitVec 64) )
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access postsize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                setsize 63)]))) || (postsize == (Sail.BitVec.castWidth (m := 64) (Zeros (n := 64))))) "armcert/armcert_c27.sail:877.70-877.71"
        ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb postsize 3 0)) == 0b0000#4) "armcert/armcert_c27.sail:878.41-878.42"
        let zero_size_exceptions ← (( do (MemSetZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt setsize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)])) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                      options_name is_setg))
                else (pure (())))
            else
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)])) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                      options_name is_setg))
                else (pure (()))))
        else (pure (()))
        let stagesetsize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagesetsize : (BitVec 64) := (setsize - postsize)
              let w__9 ← (( do (MemSetParametersIllformedM toaddress setsize is_setg) ) : SailM
                Bool )
              if (w__9 : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                    options_name is_setg))
              else (pure (()))
              (pure (stagesetsize)))
          else
            (do
              let stagesetsize : (BitVec 64) := postsize
              let w__11 ← (( do
                if (((setsize != postsize) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    (MemSetParametersIllformedE toaddress setsize is_setg)) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue
                    options_name is_setg))
              else (pure (()))
              (pure (stagesetsize))) ) : SailM (BitVec 64) )
        if (((setsize != (Sail.BitVec.castWidth (m := 64) (Zeros (n := 64)))) && (! (IsAligned__1
                 toaddress TAG_GRANULE))) : Bool)
        then
          (do
            let w__12 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
            (AArch64_Abort toaddress w__12))
        else (pure (()))
        if ((! (IsAligned__1 setsize TAG_GRANULE)) : Bool)
        then
          (do
            let w__13 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
            (AArch64_Abort toaddress w__13))
        else (pure (()))
        (pure ((nzcv, setsize, stagesetsize, toaddress)))) ) : SailM
    ((BitVec 4) × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
  let tagstep ← (( do (undefined_int_at (← occLabel 4775) ()) ) : SailM Int )
  let tag ← (( do (undefined_bitvector_at (← occLabel 4776) 4) ) : SailM (BitVec 4) )
  let tagaddr ← (( do (undefined_bitvector_at (← occLabel 4777) 64) ) : SailM (BitVec 64) )
  let w__14 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      (SPESampleMemSet ()))
  else (pure (()))
  let (setsize, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, setsize, stagesetsize, tag, tagaddr, tagstep) ← (( do
          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (B, setsize, stagesetsize, tag, tagaddr, tagstep) => (pure ((BitVec.toInt
                stagesetsize) <b 0))) (B, setsize, stagesetsize, tag, tagaddr, tagstep)
            fun (B, setsize, stagesetsize, tag, tagaddr, tagstep) => do
              let w__15 ← (( do
                (SETSizeChoice toaddress setsize 16 (Neg.neg (BitVec.toInt stagesetsize))) ) : SailM
                Int )
              let B : Int := (w__15 : Int)
              ArmFull.assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagesetsize))) "armcert/armcert_c27.sail:931.54-931.55"
              ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (integer_subrange B 3 0)) == 0b0000#4) "armcert/armcert_c27.sail:932.38-932.39"
              let B : Int := B
              ArmFull.assert ((B *i 8) ≥b 0) "armcert/armcert_c27.sail:935.48-935.49"
              (Mem_set (toaddress + setsize) (Sail.Int.toNatChecked (B)) accdesc
                (Sail.BitVec.castWidth (BitVec.replicateBits data (Sail.Int.toNatChecked (B)))))
              let tagstep : Int := (fdiv_int B 16)
              let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress (toaddress + setsize))
              let (tagaddr, tagstep) ← (( do
                let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (tagaddr, tagstep) => (pure (tagstep >b 0))) (tagaddr, tagstep)
                  fun (tagaddr, tagstep) => do
                    let tagaddr : (BitVec 64) :=
                      (BitVec.addInt (toaddress + setsize) ((tagstep -i 1) *i 16))
                    (AArch64_MemTag_set tagaddr accdesc tag)
                    let tagstep : Int := (tagstep -i 1)
                    (pure ((tagaddr, tagstep)))
                (pure loop_vars_1) ) : SailM ((BitVec 64) × Int) )
              let setsize : (BitVec 64) := (BitVec.addInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.addInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 setsize))
              else (pure (()))
              (pure ((B, setsize, stagesetsize, tag, tagaddr, tagstep)))
          (pure loop_vars) ) : SailM
          (Int × (BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × Int) )
        (pure ((setsize, toaddress))))
    else
      (do
        let (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress) ← (( do
          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress) => (pure ((BitVec.toNat
                stagesetsize) >b 0))) (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress)
            fun (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress) => do
              let w__16 ← (( do (SETSizeChoice toaddress setsize 16 (BitVec.toNat stagesetsize)) )
                : SailM Int )
              let B : Int := (w__16 : Int)
              ArmFull.assert (B ≤b (BitVec.toNat stagesetsize)) "armcert/armcert_c27.sail:955.42-955.43"
              ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (integer_subrange B 3 0)) == 0b0000#4) "armcert/armcert_c27.sail:956.38-956.39"
              let B : Int := B
              ArmFull.assert ((B *i 8) ≥b 0) "armcert/armcert_c27.sail:959.48-959.49"
              (Mem_set toaddress (Sail.Int.toNatChecked (B)) accdesc
                (Sail.BitVec.castWidth (BitVec.replicateBits data (Sail.Int.toNatChecked (B)))))
              let tagstep : Int := (fdiv_int B 16)
              let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress toaddress)
              let (tagaddr, tagstep) ← (( do
                let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (tagaddr, tagstep) => (pure (tagstep >b 0))) (tagaddr, tagstep)
                  fun (tagaddr, tagstep) => do
                    let tagaddr : (BitVec 64) := (BitVec.addInt toaddress ((tagstep -i 1) *i 16))
                    (AArch64_MemTag_set tagaddr accdesc tag)
                    let tagstep : Int := (tagstep -i 1)
                    (pure ((tagaddr, tagstep)))
                (pure loop_vars_1) ) : SailM ((BitVec 64) × Int) )
              let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
              let setsize : (BitVec 64) := (BitVec.subInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.subInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 setsize)
                  (X_set d 64 toaddress))
              else (pure (()))
              (pure ((B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress)))
          (pure loop_vars) ) : SailM
          (Int × (BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × Int × (BitVec 64)) )
        (pure ((setsize, toaddress)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 setsize)
      (X_set d 64 toaddress)
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__17 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__20 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


end ArmFull.Functions
