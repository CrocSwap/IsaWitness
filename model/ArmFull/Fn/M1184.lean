import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0061
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0204
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0237
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0852
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

/-- Type quantifiers: datasize : Nat, esize : Nat, index : Int, m : Int, n : Nat, k_replicate : Bool, selem
  : Nat, t__arg : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  List.elem selem [1, 2, 3, 4] ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_memory_vector_single_no_wb_ordered (datasize : Nat) (esize : Nat) (index : Int) (m : Int) (memop : MemOp) (n : Nat) (replicate : Bool) (selem : Nat) (t__arg : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let t : Int := t__arg
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4392) 64) ) : SailM (BitVec 64) )
  let rval ← (( do (undefined_bitvector_at (← occLabel 4393) 128) ) : SailM (BitVec 128) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4394)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let ebytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let accdesc ← (( do (CreateAccDescASIMDAcqRel memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let offs : (BitVec 64) := (Zeros (n := 64))
  let offs ← (( do
    if (replicate : Bool)
    then
      (do
        let (element, offs, t) ← (( do
          let loop_s_lower : Nat := 0
          let loop_s_upper : Nat := (Sail.Int.toNatChecked ((selem -i 1)))
          (do
            let mut loop_vars := (element, offs, t)
            for s in [loop_s_lower:loop_s_upper:1]i do
              let (element, offs, t) := loop_vars
              loop_vars ← do
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Mem_read (address + offs) ebytes accdesc)) ) :
                  SailM (BitVec (esize / 8 * 8)) )
                let element := ((Sail.BitVec.castWidth w__2) : (BitVec esize))
                (V_set t datasize
                  (Sail.BitVec.castWidth (BitVec.replicateBits element
                    (Sail.Int.toNatChecked ((Int.ediv datasize esize))))))
                let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
                let t : Int := (fmod_int (t +i 1) 32)
                (pure ((element, offs, t)))
            (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 64) × Int) )
        (pure (offs)))
    else
      (do
        let (offs, rval, t) ← (( do
          let loop_s_lower : Nat := 0
          let loop_s_upper : Nat := (Sail.Int.toNatChecked ((selem -i 1)))
          (do
            let mut loop_vars := (offs, rval, t)
            for s in [loop_s_lower:loop_s_upper:1]i do
              let (offs, rval, t) := loop_vars
              loop_vars ← do
                let w__3 ← (( do (V_read t 128) ) : SailM (BitVec 128) )
                let rval := (w__3 : (BitVec 128))
                let rval ← (( do
                  if ((BEq.beq memop MemOp_LOAD) : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Mem_read (address + offs) ebytes accdesc)) )
                        : SailM (BitVec (esize / 8 * 8)) )
                      let w__5 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_set rval index esize
                          (Sail.BitVec.castWidth w__4))) ) : SailM (BitVec 128) )
                      let rval := (w__5 : (BitVec 128))
                      (V_set t 128 rval)
                      (pure (rval)))
                  else
                    (do
                      let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read rval index esize))
                        ) : SailM (BitVec ((Sail.Int.toNatChecked ebytes) * 8)) )
                      (Mem_set (address + offs) ebytes accdesc (Sail.BitVec.castWidth w__6))
                      (pure (rval))) ) : SailM (BitVec 128) )
                let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
                let t : Int := (fmod_int (t +i 1) 32)
                (pure ((offs, rval, t)))
            (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 128) × Int) )
        (pure (offs))) ) : SailM (BitVec 64) )
  let w__7 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))
  if (wback : Bool)
  then
    (do
      let offs ← (( do
        if ((m != 31) : Bool)
        then
          (do
            (X_read m 64))
        else (pure (offs)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set (address + offs)))
      else
        (do
          (X_set n 64 (address + offs))))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, n : Nat, offset : Nat, regsize : Nat, t : Nat, k_tagchecked :
  Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧
  List.elem offset [0, 1, 2, 4, 8] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_ordered_rcpc (datasize : Nat) (n : Nat) (offset : Nat) (regsize : Nat) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4397) 64) ) : SailM (BitVec 64) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
  let accdesc ← (( do (CreateAccDescLDAcqPC tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do ((Sail.BitVec.castWidth ) <$> ((Mem_read address dbytes accdesc))) ) : SailM
    (BitVec datasize) )
  ArmFull.assert (regsize ≥b datasize) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:27327.44-27327.45"
  (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (let address : (BitVec 64) := (BitVec.addInt address offset)
          (pure (address))) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__3 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let ar : (BitVec 1) := 1#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_postindex : Bool, regsize : Nat, k_rt_unknown
  : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (datasize : Nat) (memop : MemOp) (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4398) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4399)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (undefined_AccessDescriptor (← occLabel 4400) ()) ) : SailM
    AccessDescriptor )
  let accdesc ← (( do
    if ((BEq.beq memop MemOp_LOAD) : Bool)
    then
      (do
        (CreateAccDescLDAcqPC tagchecked))
    else
      (do
        if ((BEq.beq memop MemOp_STORE) : Bool)
        then
          (do
            (CreateAccDescAcqRel memop tagchecked))
        else (pure (accdesc))) ) : SailM AccessDescriptor )
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
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:27521.72-27521.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:27524.73-27524.74"
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
  let w__7 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, n : Nat, k_postindex : Bool, t : Nat, k_tagchecked : Bool, k_wback
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (datasize : Nat) (memop : MemOp) (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4428) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4429)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMDAcqRel memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28335.62-28335.63"
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28341.62-28341.63"
      (V_set t datasize (Sail.BitVec.castWidth data)))
  | _ => (pure (()))
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_limitedordered : Bool, n : Nat, offset : Int, regsize : Nat, k_rt_unknown
  : Bool, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_ordered (datasize : Nat) (limitedordered : Bool) (memop : MemOp) (n : Nat) (offset : Int) (regsize : Nat) (rt_unknown : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4430) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4431)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
  let accdesc ← (( do (undefined_AccessDescriptor (← occLabel 4432) ()) ) : SailM
    AccessDescriptor )
  let accdesc ← (( do
    if (limitedordered : Bool)
    then
      (do
        (CreateAccDescLOR memop tagchecked))
    else
      (do
        (CreateAccDescAcqRel memop tagchecked)) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  match memop with
  | .MemOp_STORE =>
    (do
      let address : (BitVec 64) := (BitVec.addInt address offset)
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let _ : Unit := (AArch64_SetLSInstructionSyndrome dbytes false t (regsize == 64) true)
      (Mem_set address dbytes accdesc (Sail.BitVec.castWidth data))
      if (wback : Bool)
      then
        (do
          if ((n == 31) : Bool)
          then
            (do
              (SP_set address))
          else
            (do
              (X_set n 64 address)))
      else (pure (())))
  | .MemOp_LOAD =>
    (do
      let _ : Unit := (AArch64_SetLSInstructionSyndrome dbytes false t (regsize == 64) true)
      let data ← (( do ((Sail.BitVec.castWidth ) <$> ((Mem_read address dbytes accdesc))) ) :
        SailM (BitVec datasize) )
      ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28464.69-28464.70"
      (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize))))
  | _ => (pure (()))
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let ar : (BitVec 1) := 1#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := (BEq.beq memop MemOp_LOAD)
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


/-- Type quantifiers: k_acqrel : Bool, datasize : Nat, elsize : Nat, n : Nat, k_pair : Bool, regsize
  : Nat, k_rn_unknown : Bool, k_rt_unknown : Bool, s : Nat, t : Nat, t2 : Nat, k_tagchecked : Bool, 0
  ≤ t2 ∧
  t2 ≤ 31 ∧
  0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ s ∧
  s ≤ 31 ∧
  List.elem regsize [32, 64] ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem elsize [32, 64] ∧ List.elem datasize [32, 64, 128] -/
def execute_aarch64_instrs_memory_exclusive_pair (acqrel : Bool) (datasize : Nat) (elsize : Nat) (memop : MemOp) (n : Nat) (pair : Bool) (regsize : Nat) (rn_unknown : Bool) (rt_unknown : Bool) (s : Nat) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4433) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4434)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
  let accdesc ← (( do (CreateAccDescExLDST memop acqrel tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        if (rn_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
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
            if (pair : Bool)
            then
              (do
                let el1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (X_read t
                    (Sail.Int.toNatChecked ((Int.ediv datasize 2))))) ) : SailM
                  (BitVec (datasize / 2)) )
                let el2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (X_read t2
                    (Sail.Int.toNatChecked ((Int.ediv datasize 2))))) ) : SailM
                  (BitVec (datasize / 2)) )
                let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
                let w__5 : (BitVec datasize) :=
                  if (w__4 : Bool)
                  then (Sail.BitVec.castWidth (el1 +++ el2))
                  else (Sail.BitVec.castWidth (el2 +++ el1))
                (pure ((w__5 : (BitVec datasize)))))
            else
              (do
                ArmFull.assert ((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28968.61-28968.62"
                ((Sail.BitVec.castWidth ) <$> (X_read t datasize)))) ) : SailM (BitVec datasize) )
      let status : (BitVec 1) := 1#1
      let w__7 ← (( do (AArch64_ExclusiveMonitorsPass address dbytes) ) : SailM Bool )
      let status ← (( do
        if (w__7 : Bool)
        then
          (do
            (Mem_set address dbytes accdesc (Sail.BitVec.castWidth data))
            (ExclusiveMonitorsStatus ()))
        else
          (do
            let w__9 ← (( do readReg SPESampleInFlight ) : SailM Bool )
            if (w__9 : Bool)
            then
              (do
                (SPESetDataVirtualAddress address))
            else (pure (()))
            (pure (status))) ) : SailM (BitVec 1) )
      (X_set s 32 (Sail.BitVec.zeroExtend status 32)))
  | .MemOp_LOAD =>
    (do
      (AArch64_SetExclusiveMonitors address dbytes)
      if (pair : Bool)
      then
        (do
          if (rt_unknown : Bool)
          then
            (do
              ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28984.58-28984.59"
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
                (BitVec datasize) )
              (X_set t datasize (Sail.BitVec.castWidth w__10)))
          else
            (do
              if ((elsize == 32) : Bool)
              then
                (do
                  let data ← (( do
                    ((Sail.BitVec.castWidth ) <$> ((Mem_read address dbytes accdesc))) ) : SailM
                    (BitVec datasize) )
                  let w__11 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
                  if (w__11 : Bool)
                  then
                    (do
                      ArmFull.assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28989.110-28989.111"
                      ArmFull.assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28990.96-28990.97"
                      (X_set t (Sail.Int.toNatChecked ((datasize -i elsize)))
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((datasize -i 1))) elsize)))
                      (X_set t2 elsize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((elsize -i 1))) 0))))
                  else
                    (do
                      (X_set t elsize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((elsize -i 1))) 0)))
                      ArmFull.assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28995.110-28995.111"
                      ArmFull.assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:28996.96-28996.97"
                      (X_set t2 (Sail.Int.toNatChecked ((datasize -i elsize)))
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((datasize -i 1))) elsize)))))
              else
                (do
                  if ((! (IsAligned__1 address dbytes)) : Bool)
                  then
                    (do
                      let w__12 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
                      (AArch64_Abort address w__12))
                  else (pure (()))
                  let w__13 ← (( do (Mem_read (BitVec.addInt address 0) 8 accdesc) ) : SailM
                    (BitVec (8 * 8)) )
                  (X_set t 64 w__13)
                  let w__14 ← (( do (Mem_read (BitVec.addInt address 8) 8 accdesc) ) : SailM
                    (BitVec (8 * 8)) )
                  (X_set t2 64 w__14))))
      else
        (do
          let data ← (( do ((Sail.BitVec.castWidth ) <$> ((Mem_read address dbytes accdesc))) ) :
            SailM (BitVec datasize) )
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29008.73-29008.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | _ => (pure (()))
  let w__15 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if (acqrel : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 1#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := (BEq.beq memop MemOp_LOAD)
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


/-- Type quantifiers: k_acqrel : Bool, datasize : Nat, elsize : Nat, n : Nat, k_pair : Bool, regsize
  : Nat, k_rn_unknown : Bool, k_rt_unknown : Bool, s : Nat, t : Nat, t2 : Nat, k_tagchecked : Bool, 0
  ≤ t2 ∧
  t2 ≤ 31 ∧
  0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ s ∧
  s ≤ 31 ∧
  List.elem regsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ List.elem elsize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] -/
def execute_aarch64_instrs_memory_exclusive_single (acqrel : Bool) (datasize : Nat) (elsize : Nat) (memop : MemOp) (n : Nat) (pair : Bool) (regsize : Nat) (rn_unknown : Bool) (rt_unknown : Bool) (s : Nat) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4435) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4436)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
  let accdesc ← (( do (CreateAccDescExLDST memop acqrel tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        if (rn_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
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
            if (pair : Bool)
            then
              (do
                ArmFull.assert (((Int.ediv datasize 2) == 8) || (((Int.ediv datasize 2) == 16) || (((Int.ediv
                          datasize 2) == 32) || ((Int.ediv datasize 2) == 64)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29382.135-29382.136"
                let el1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (X_read t
                    (Sail.Int.toNatChecked ((Int.ediv datasize 2))))) ) : SailM
                  (BitVec (datasize / 2)) )
                let el2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (X_read t2
                    (Sail.Int.toNatChecked ((Int.ediv datasize 2))))) ) : SailM
                  (BitVec (datasize / 2)) )
                let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
                let w__5 : (BitVec datasize) :=
                  if (w__4 : Bool)
                  then (Sail.BitVec.castWidth (el1 +++ el2))
                  else (Sail.BitVec.castWidth (el2 +++ el1))
                (pure ((w__5 : (BitVec datasize)))))
            else
              (do
                ArmFull.assert ((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29387.61-29387.62"
                ((Sail.BitVec.castWidth ) <$> (X_read t datasize)))) ) : SailM (BitVec datasize) )
      let status : (BitVec 1) := 1#1
      let w__7 ← (( do (AArch64_ExclusiveMonitorsPass address dbytes) ) : SailM Bool )
      let status ← (( do
        if (w__7 : Bool)
        then
          (do
            (Mem_set address dbytes accdesc (Sail.BitVec.castWidth data))
            (ExclusiveMonitorsStatus ()))
        else
          (do
            let w__9 ← (( do readReg SPESampleInFlight ) : SailM Bool )
            if (w__9 : Bool)
            then
              (do
                (SPESetDataVirtualAddress address))
            else (pure (()))
            (pure (status))) ) : SailM (BitVec 1) )
      (X_set s 32 (Sail.BitVec.zeroExtend status 32)))
  | .MemOp_LOAD =>
    (do
      (AArch64_SetExclusiveMonitors address dbytes)
      if (pair : Bool)
      then
        (do
          if (rt_unknown : Bool)
          then
            (do
              ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29403.58-29403.59"
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
                (BitVec datasize) )
              (X_set t datasize (Sail.BitVec.castWidth w__10)))
          else
            (do
              if ((elsize == 32) : Bool)
              then
                (do
                  let data ← (( do
                    ((Sail.BitVec.castWidth ) <$> ((Mem_read address dbytes accdesc))) ) : SailM
                    (BitVec datasize) )
                  let w__11 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
                  if (w__11 : Bool)
                  then
                    (do
                      ArmFull.assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29408.110-29408.111"
                      ArmFull.assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29409.96-29409.97"
                      (X_set t (Sail.Int.toNatChecked ((datasize -i elsize)))
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((datasize -i 1))) elsize)))
                      (X_set t2 elsize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((elsize -i 1))) 0))))
                  else
                    (do
                      ArmFull.assert ((0 ≤b (elsize -i 1)) && ((elsize -i 1) <b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29413.85-29413.86"
                      (X_set t elsize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((elsize -i 1))) 0)))
                      ArmFull.assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29415.110-29415.111"
                      ArmFull.assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29416.96-29416.97"
                      (X_set t2 (Sail.Int.toNatChecked ((datasize -i elsize)))
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((datasize -i 1))) elsize)))))
              else
                (do
                  if ((! (IsAligned__1 address dbytes)) : Bool)
                  then
                    (do
                      let w__12 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
                      (AArch64_Abort address w__12))
                  else (pure (()))
                  let w__13 ← (( do (Mem_read (BitVec.addInt address 0) 8 accdesc) ) : SailM
                    (BitVec (8 * 8)) )
                  (X_set t 64 w__13)
                  let w__14 ← (( do (Mem_read (BitVec.addInt address 8) 8 accdesc) ) : SailM
                    (BitVec (8 * 8)) )
                  (X_set t2 64 w__14))))
      else
        (do
          let data ← (( do ((Sail.BitVec.castWidth ) <$> ((Mem_read address dbytes accdesc))) ) :
            SailM (BitVec datasize) )
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:29428.73-29428.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | _ => (pure (()))
  let w__15 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if (acqrel : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 1#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := (BEq.beq memop MemOp_LOAD)
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


end ArmFull.Functions
