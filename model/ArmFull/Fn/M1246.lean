module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0204
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0215
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0255
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0956
public import ArmFull.Fn.M1138
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
                          datasize 2) == 32) || ((Int.ediv datasize 2) == 64)))) "sail-inputs/15-instrs64.sail:29382.135-29382.136"
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
                ArmFull.assert ((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) "sail-inputs/15-instrs64.sail:29387.61-29387.62"
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
              ArmFull.assert ((datasize == 32) || (datasize == 64)) "sail-inputs/15-instrs64.sail:29403.58-29403.59"
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
                      ArmFull.assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "sail-inputs/15-instrs64.sail:29408.110-29408.111"
                      ArmFull.assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "sail-inputs/15-instrs64.sail:29409.96-29409.97"
                      (X_set t (Sail.Int.toNatChecked ((datasize -i elsize)))
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((datasize -i 1))) elsize)))
                      (X_set t2 elsize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((elsize -i 1))) 0))))
                  else
                    (do
                      ArmFull.assert ((0 ≤b (elsize -i 1)) && ((elsize -i 1) <b datasize)) "sail-inputs/15-instrs64.sail:29413.85-29413.86"
                      (X_set t elsize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
                          (Sail.Int.toNatChecked ((elsize -i 1))) 0)))
                      ArmFull.assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "sail-inputs/15-instrs64.sail:29415.110-29415.111"
                      ArmFull.assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "sail-inputs/15-instrs64.sail:29416.96-29416.97"
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
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "sail-inputs/15-instrs64.sail:29428.73-29428.74"
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:31021.62-31021.63"
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:31034.62-31034.63"
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:31176.62-31176.63"
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
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:31189.62-31189.63"
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


end ArmFull.Functions
