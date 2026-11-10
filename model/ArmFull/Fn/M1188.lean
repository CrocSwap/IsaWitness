import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0017
import ArmFull.Fn.M0044
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0202
import ArmFull.Fn.M0216
import ArmFull.Fn.M0237
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0924
import ArmFull.Fn.M1087
import ArmFull.Fn.M1142
import ArmFull.Fn.M1155
import ArmFull.Fn.M1158

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

/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0
  ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagpairpost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4984) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    if ((t == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read t 64)) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
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
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then
        (do
          let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
          (AArch64_Abort address w__4))
      else (pure (()))
      (Mem_set address TAG_GRANULE accdesc
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((TAG_GRANULE *i 8)))))))
      (Mem_set (BitVec.addInt address TAG_GRANULE) TAG_GRANULE accdesc
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((TAG_GRANULE *i 8))))))))
  else (pure (()))
  (AArch64_MemTag_set address accdesc tag)
  (AArch64_MemTag_set (BitVec.addInt address TAG_GRANULE) accdesc tag)
  if (writeback : Bool)
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


/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0
  ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagpost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4994) 64) ) : SailM (BitVec 64) )
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
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then
        (do
          let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
          (AArch64_Abort address w__2))
      else (pure (()))
      (Mem_set address TAG_GRANULE accdesc
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((TAG_GRANULE *i 8))))))))
  else (pure (()))
  let data ← (( do
    if ((t == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read t 64)) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
  (AArch64_MemTag_set address accdesc tag)
  if (writeback : Bool)
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


/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, t2 : Nat, k_writeback : Bool, 0 ≤ t2
  ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (t2 : Nat) (writeback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4996) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let data1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let data2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__2))
  else (pure (()))
  (Mem_set address 8 accdesc data1)
  (Mem_set (BitVec.addInt address 8) 8 accdesc data2)
  (AArch64_MemTag_set address accdesc (AArch64_AllocationTagFromAddress address))
  if (writeback : Bool)
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


/-- Type quantifiers: datasize : Nat, n : Nat, offset : Int, k_postindex : Bool, k_rt_unknown : Bool, t
  : Nat, t2 : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t2 ∧
  t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_ordered_pair_stilp (datasize : Nat) (memop : MemOp) (n : Nat) (offset : Int) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4997) 64) ) : SailM (BitVec 64) )
  let data1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4998)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let data2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4999)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
  let accdesc ← (( do (CreateAccDescAcqRel memop tagchecked) ) : SailM AccessDescriptor )
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
    then (BitVec.addInt address offset)
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
      let w__6 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let full_data ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5000)
              (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
          let w__7 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
          let full_data : (BitVec (2 * datasize)) :=
            if (w__7 : Bool)
            then (Sail.BitVec.castWidth (data1 +++ data2))
            else (Sail.BitVec.castWidth (data2 +++ data1))
          let ispair : Bool := true
          let highestAddressfirst : Bool := ((! postindex) && (offset <b 0))
          (Mem_set__2 address (Sail.Int.toNatChecked ((2 *i dbytes))) accdesc ispair
            highestAddressfirst (Sail.BitVec.castWidth full_data)))
      else
        (do
          if (((! postindex) && (offset <b 0)) : Bool)
          then
            (do
              (Mem_set (BitVec.addInt address dbytes) dbytes accdesc (Sail.BitVec.castWidth data2))
              (Mem_set (BitVec.addInt address 0) dbytes accdesc (Sail.BitVec.castWidth data1)))
          else
            (do
              (Mem_set (BitVec.addInt address 0) dbytes accdesc (Sail.BitVec.castWidth data1))
              (Mem_set (BitVec.addInt address dbytes) dbytes accdesc (Sail.BitVec.castWidth data2)))))
  | .MemOp_LOAD =>
    (do
      let w__8 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
      let (data1, data2) ← (( do
        if (w__8 : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do
              ((Sail.BitVec.castWidth ) <$> ((Mem_read__1 address
                (Sail.Int.toNatChecked ((2 *i dbytes))) accdesc ispair))) ) : SailM
              (BitVec (2 * datasize)) )
            let w__9 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
            let (data1, data2) : ((BitVec datasize) × (BitVec datasize)) :=
              if (w__9 : Bool)
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
            let w__10 ← (( do
              ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address 0) dbytes accdesc)) ) :
              SailM (BitVec (datasize / 8 * 8)) )
            let data1 := ((Sail.BitVec.castWidth w__10) : (BitVec datasize))
            let w__11 ← (( do
              ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address dbytes) dbytes accdesc))
              ) : SailM (BitVec (datasize / 8 * 8)) )
            let data2 := ((Sail.BitVec.castWidth w__11) : (BitVec datasize))
            (pure ((data1, data2)))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let w__12 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data1 := (w__12 : (BitVec datasize))
            let w__13 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data2 := (w__13 : (BitVec datasize))
            (pure ((data1, data2))))
        else (pure ((data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      (X_set t datasize (Sail.BitVec.castWidth data1))
      (X_set t2 datasize (Sail.BitVec.castWidth data2)))
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
            then (BitVec.addInt address offset)
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
  let w__15 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0
  ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 5003) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    if ((t == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read t 64)) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
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
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then
        (do
          let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
          (AArch64_Abort address w__4))
      else (pure (()))
      (Mem_set address TAG_GRANULE accdesc
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((TAG_GRANULE *i 8)))))))
      (Mem_set (BitVec.addInt address TAG_GRANULE) TAG_GRANULE accdesc
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((TAG_GRANULE *i 8))))))))
  else (pure (()))
  (AArch64_MemTag_set address accdesc tag)
  (AArch64_MemTag_set (BitVec.addInt address TAG_GRANULE) accdesc tag)
  if (writeback : Bool)
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


/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0
  ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 5004) 64) ) : SailM (BitVec 64) )
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
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then
        (do
          let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
          (AArch64_Abort address w__2))
      else (pure (()))
      (Mem_set address TAG_GRANULE accdesc
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((TAG_GRANULE *i 8))))))))
  else (pure (()))
  let data ← (( do
    if ((t == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read t 64)) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
  (AArch64_MemTag_set address accdesc tag)
  if (writeback : Bool)
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


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagandzeroarray (n : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let data ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (Sail.BitVec.extractLsb data 3 0)
  let address ← (( do (undefined_bitvector_at (← occLabel 5005) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__3 ← (( do readReg DCZID_EL0 ) : SailM (BitVec 64) )
  let size : Nat :=
    (Sail.Int.toNatChecked ((4 *i (2 ^i (BitVec.toNat (_get_DCZID_EL0_Type_BS w__3))))))
  let address : (BitVec 64) := (Align_bits address size)
  let count : Int := (Int.shiftr size LOG2_TAG_GRANULE)
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  let address ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (count -i 1)
    (do
      let mut loop_vars := address
      for i in [loop_i_lower:loop_i_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          (AArch64_MemTag_set address accdesc tag)
          (Mem_set address TAG_GRANULE accdesc
            (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((8 *i TAG_GRANULE)))))))
          let address : (BitVec 64) := (BitVec.addInt address TAG_GRANULE)
          (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (pure (()))


def decode_FTSMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FTSMUL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FTSMUL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FTSMUL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FTSMUL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FTSMUL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FTMAD_Z_ZZI__ (size : (BitVec 2)) (imm3 : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  let imm : Int := (BitVec.toNat imm3)
  match VL with
  | 128 =>
    (do
      (execute_FTMAD_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FTMAD_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FTMAD_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FTMAD_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FTMAD_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FMMLA_Z_ZZZ_S (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP32MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  match VL with
  | 128 =>
    (do
      (execute_FMMLA_Z_ZZZ_S 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMMLA_Z_ZZZ_S 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMMLA_Z_ZZZ_S 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMMLA_Z_ZZZ_S 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMMLA_Z_ZZZ_S 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMMLA_Z_ZZZ_D (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  match VL with
  | 128 =>
    (do
      (execute_FMMLA_Z_ZZZ_D 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMMLA_Z_ZZZ_D 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMMLA_Z_ZZZ_D 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMMLA_Z_ZZZ_D 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMMLA_Z_ZZZ_D 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
