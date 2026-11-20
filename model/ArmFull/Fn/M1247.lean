module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0215
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0255
public import ArmFull.Fn.M0604
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M1197 set_option backward.proofsInPublic true @[expose] public section

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
  : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback
  : Bool, 0 ≤ t2 ∧
  t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_pair_general_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4456) 64) ) : SailM (BitVec 64) )
  let data1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4457)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let data2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4458)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
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
      let data1 ← (( do
        if ((rt_unknown && (t == n)) : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let data2 ← (( do
        if ((rt_unknown && (t2 == n)) : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t2 datasize))) ) : SailM (BitVec datasize) )
      let w__7 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let full_data ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4459)
              (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
          let w__8 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
          let full_data : (BitVec (2 * datasize)) :=
            if (w__8 : Bool)
            then (Sail.BitVec.castWidth (data1 +++ data2))
            else (Sail.BitVec.castWidth (data2 +++ data1))
          let ispair : Bool := true
          (Mem_set__1 address (Sail.Int.toNatChecked ((2 *i dbytes))) accdesc ispair
            (Sail.BitVec.castWidth full_data)))
      else
        (do
          (Mem_set (BitVec.addInt address 0) dbytes accdesc (Sail.BitVec.castWidth data1))
          (Mem_set (BitVec.addInt address dbytes) dbytes accdesc (Sail.BitVec.castWidth data2))))
  | .MemOp_LOAD =>
    (do
      let w__10 ← (( do
        (pure ((← do
              (HaveLSE2Ext ())) && ((! is_signed) : Bool))) ) : SailM Bool )
      let (data1, data2) ← (( do
        if (w__10 : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do
              ((Sail.BitVec.castWidth ) <$> ((Mem_read__1 address
                (Sail.Int.toNatChecked ((2 *i dbytes))) accdesc ispair))) ) : SailM
              (BitVec (2 * datasize)) )
            let w__11 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
            let (data1, data2) : ((BitVec datasize) × (BitVec datasize)) :=
              if (w__11 : Bool)
              then
                (let data2 : (BitVec datasize) :=
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb full_data
                    (Sail.Int.toNatChecked ((datasize -i 1))) 0))
                let data1 : (BitVec datasize) :=
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb full_data
                    (Sail.Int.toNatChecked (((2 *i datasize) -i 1))) datasize))
                (data1, data2))
              else
                (let data1 : (BitVec datasize) :=
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb full_data
                    (Sail.Int.toNatChecked ((datasize -i 1))) 0))
                let data2 : (BitVec datasize) :=
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb full_data
                    (Sail.Int.toNatChecked (((2 *i datasize) -i 1))) datasize))
                (data1, data2))
            (pure ((data1, data2))))
        else
          (do
            let w__12 ← (( do
              ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address 0) dbytes accdesc)) ) :
              SailM (BitVec (datasize / 8 * 8)) )
            let data1 := ((Sail.BitVec.castWidth w__12) : (BitVec datasize))
            let w__13 ← (( do
              ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address dbytes) dbytes accdesc))
              ) : SailM (BitVec (datasize / 8 * 8)) )
            let data2 := ((Sail.BitVec.castWidth w__13) : (BitVec datasize))
            (pure ((data1, data2)))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let w__14 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data1 := (w__14 : (BitVec datasize))
            let w__15 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data2 := (w__15 : (BitVec datasize))
            (pure ((data1, data2))))
        else (pure ((data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      if (is_signed : Bool)
      then
        (do
          (X_set t 64 (sign_extend data1 64))
          (X_set t2 64 (sign_extend data2 64)))
      else
        (do
          (X_set t datasize (Sail.BitVec.castWidth data1))
          (X_set t2 datasize (Sail.BitVec.castWidth data2))))
  | _ => (pure (()))
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
  let w__17 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__17 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, t : Nat, k_tagchecked
  : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4460) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4461)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:32419.62-32419.63"
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:32425.62-32425.63"
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


/-- Type quantifiers: k_is_signed : Bool, k_nontemporal : Bool, size : Nat, t : Nat, k_tagchecked :
  Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem size [4, 8] -/
def execute_aarch64_instrs_memory_literal_general (memop : MemOp) (nontemporal : Bool) (offset : (BitVec 64)) (is_signed : Bool) (size : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (w__0 + offset)
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4462)
      (Sail.Int.toNatChecked ((size *i 8))))) ) : SailM (BitVec (size * 8)) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__1.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  match memop with
  | .MemOp_LOAD =>
    (do
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read address size accdesc)) ) : SailM
        (BitVec (size * 8)) )
      if (is_signed : Bool)
      then
        (do
          (X_set t 64 (sign_extend data 64)))
      else
        (do
          (X_set t (Sail.Int.toNatChecked ((size *i 8))) (Sail.BitVec.castWidth data))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  | _ => (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: k_nontemporal : Bool, size : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem size [4, 8, 16] -/
def execute_aarch64_instrs_memory_literal_simdfp (nontemporal : Bool) (offset : (BitVec 64)) (size : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (w__0 + offset)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__1.EL != EL0)
  (CheckFPEnabled64 ())
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  let data ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read address size accdesc)) ) : SailM
    (BitVec (size * 8)) )
  (V_set t (Sail.Int.toNatChecked ((size *i 8))) (Sail.BitVec.castWidth data))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4463) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4464)
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
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "sail-inputs/15-instrs64.sail:32855.72-32855.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "sail-inputs/15-instrs64.sail:32858.73-32858.74"
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


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, m : Nat, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, shift : Nat, t : Nat, k_tagchecked : Bool, k_wb_unknown
  : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem shift [0, 1, 2, 3] ∧
  List.elem regsize [32, 64] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_register (datasize : Nat) (extend_type : ExtendType) (m : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (shift : Nat) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let offset ← (( do (ExtendReg m extend_type shift 64) ) : SailM (BitVec 64) )
  let address ← (( do (undefined_bitvector_at (← occLabel 4546) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4547)
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
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "sail-inputs/15-instrs64.sail:35245.72-35245.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "sail-inputs/15-instrs64.sail:35248.73-35248.74"
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


/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, shift
  : Nat, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem shift [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_register (datasize : Nat) (extend_type : ExtendType) (m : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (postindex : Bool) (shift : Nat) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let offset ← (( do (ExtendReg m extend_type shift 64) ) : SailM (BitVec 64) )
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4578) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4579)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:36272.62-36272.63"
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:36278.62-36278.63"
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


/-- Type quantifiers: n : Nat, k_nontemporal : Bool, t : Nat, k_tagchecked : Bool, k_use_key_a :
  Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_pac (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (t : Nat) (tagchecked : Bool) (use_key_a : Bool) (wback__arg : Bool) : SailM Unit := do
  let wback : Bool := wback__arg
  let address ← (( do (undefined_bitvector_at (← occLabel 4580) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let wb_unknown : Bool := false
  let auth_then_branch : Bool := true
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let (wb_unknown, wback) ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-inputs/15-instrs64.sail:36386.113-36386.114"
        match c with
        | .Constraint_WBSUPPRESS =>
          (let wback : Bool := false
          (pure ((wb_unknown, wback))))
        | .Constraint_UNKNOWN =>
          (let wb_unknown : Bool := true
          (pure ((wb_unknown, wback))))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure ((wb_unknown, wback))))
        | _ => (pure ((wb_unknown, wback))))
    else (pure ((wb_unknown, wback))) ) : SailM (Bool × Bool) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit :=
    if ((! wback) : Bool)
    then (AArch64_SetLSInstructionSyndrome 8 false t true false)
    else ()
  let address ← (( do
    if (use_key_a : Bool)
    then
      (do
        let w__3 ← (( do (X_read 31 64) ) : SailM (BitVec 64) )
        (AuthDA address w__3 auth_then_branch))
    else
      (do
        let w__5 ← (( do (X_read 31 64) ) : SailM (BitVec 64) )
        (AuthDB address w__5 auth_then_branch)) ) : SailM (BitVec 64) )
  if ((n == 31) : Bool)
  then
    (do
      (CheckSPAlignment ()))
  else (pure (()))
  let address : (BitVec 64) := (address + offset)
  let data ← (( do (Mem_read address 8 accdesc) ) : SailM (BitVec 64) )
  (X_set t 64 data)
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else (pure (address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__8 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


end ArmFull.Functions
