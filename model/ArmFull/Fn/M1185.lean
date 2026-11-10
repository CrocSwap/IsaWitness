import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0049
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0840
import ArmFull.Fn.M1087
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

/-- Type quantifiers: datasize : Nat, n : Nat, offset : Int, k_postindex : Bool, k_rt_unknown : Bool, t
  : Nat, t2 : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t2 ∧
  t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_ordered_pair_ldiapp (datasize : Nat) (memop : MemOp) (n : Nat) (offset : Int) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4441) 64) ) : SailM (BitVec 64) )
  let data1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4442)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let data2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4443)
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
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4444)
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


/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown
  : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t2 ∧
  t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_pair_general_no_alloc (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4447) 64) ) : SailM (BitVec 64) )
  let data1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4448)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let data2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4449)
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
      (Mem_set (BitVec.addInt address 0) dbytes accdesc (Sail.BitVec.castWidth data1))
      (Mem_set (BitVec.addInt address dbytes) dbytes accdesc (Sail.BitVec.castWidth data2)))
  | .MemOp_LOAD =>
    (do
      let w__7 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
      let (data1, data2) ← (( do
        if (w__7 : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do
              ((Sail.BitVec.castWidth ) <$> ((Mem_read__1 address
                (Sail.Int.toNatChecked ((2 *i dbytes))) accdesc ispair))) ) : SailM
              (BitVec (2 * datasize)) )
            let w__8 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
            let (data1, data2) : ((BitVec datasize) × (BitVec datasize)) :=
              if (w__8 : Bool)
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
            let w__9 ← (( do
              ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address 0) dbytes accdesc)) ) :
              SailM (BitVec (datasize / 8 * 8)) )
            let data1 := ((Sail.BitVec.castWidth w__9) : (BitVec datasize))
            let w__10 ← (( do
              ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address dbytes) dbytes accdesc))
              ) : SailM (BitVec (datasize / 8 * 8)) )
            let data2 := ((Sail.BitVec.castWidth w__10) : (BitVec datasize))
            (pure ((data1, data2)))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let w__11 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data1 := (w__11 : (BitVec datasize))
            let w__12 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data2 := (w__12 : (BitVec datasize))
            (pure ((data1, data2))))
        else (pure ((data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      (X_set t datasize (Sail.BitVec.castWidth data1))
      (X_set t2 datasize (Sail.BitVec.castWidth data2)))
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
  let w__13 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown
  : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t2 ∧
  t2 ≤ 31 ∧
  0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64, 128, 256] -/
def execute_aarch64_instrs_memory_pair_simdfp_no_alloc (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4450) 64) ) : SailM (BitVec 64) )
  let data1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4451)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let data2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4452)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31021.62-31021.63"
      let data1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      let data2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t2 datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set (BitVec.addInt address 0) dbytes accdesc (Sail.BitVec.castWidth data1))
      (Mem_set (BitVec.addInt address dbytes) dbytes accdesc (Sail.BitVec.castWidth data2)))
  | .MemOp_LOAD =>
    (do
      let w__2 ← (( do
        ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address 0) dbytes accdesc)) ) : SailM
        (BitVec (datasize / 8 * 8)) )
      let data1 : (BitVec datasize) := (Sail.BitVec.castWidth (w__2 : (BitVec (datasize / 8 * 8))))
      let w__3 ← (( do
        ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address dbytes) dbytes accdesc)) ) :
        SailM (BitVec (datasize / 8 * 8)) )
      let data2 : (BitVec datasize) := (Sail.BitVec.castWidth (w__3 : (BitVec (datasize / 8 * 8))))
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data1 := (w__4 : (BitVec datasize))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data2 := (w__5 : (BitVec datasize))
            (pure ((data1, data2))))
        else (pure ((data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31034.62-31034.63"
      (V_set t datasize (Sail.BitVec.castWidth data1))
      (V_set t2 datasize (Sail.BitVec.castWidth data2)))
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
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown
  : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t2 ∧
  t2 ≤ 31 ∧
  0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64, 128, 256] -/
def execute_aarch64_instrs_memory_pair_simdfp_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4453) 64) ) : SailM (BitVec 64) )
  let data1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4454)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let data2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4455)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let dbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize 8)))
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31176.62-31176.63"
      let data1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      let data2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t2 datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set (BitVec.addInt address 0) dbytes accdesc (Sail.BitVec.castWidth data1))
      (Mem_set (BitVec.addInt address dbytes) dbytes accdesc (Sail.BitVec.castWidth data2)))
  | .MemOp_LOAD =>
    (do
      let w__2 ← (( do
        ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address 0) dbytes accdesc)) ) : SailM
        (BitVec (datasize / 8 * 8)) )
      let data1 : (BitVec datasize) := (Sail.BitVec.castWidth (w__2 : (BitVec (datasize / 8 * 8))))
      let w__3 ← (( do
        ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.addInt address dbytes) dbytes accdesc)) ) :
        SailM (BitVec (datasize / 8 * 8)) )
      let data2 : (BitVec datasize) := (Sail.BitVec.castWidth (w__3 : (BitVec (datasize / 8 * 8))))
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data1 := (w__4 : (BitVec datasize))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
              (BitVec datasize) )
            let data2 := (w__5 : (BitVec datasize))
            (pure ((data1, data2))))
        else (pure ((data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31189.62-31189.63"
      (V_set t datasize (Sail.BitVec.castWidth data1))
      (V_set t2 datasize (Sail.BitVec.castWidth data2)))
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
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


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


end ArmFull.Functions
