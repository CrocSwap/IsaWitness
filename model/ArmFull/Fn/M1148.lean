import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0020
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0175
import ArmFull.Fn.M0215
import ArmFull.Fn.M0228
import ArmFull.Fn.M0852
import ArmFull.Fn.M0925
import ArmFull.Fn.M1087
import ArmFull.Fn.M1095
import ArmFull.Fn.M1096
import ArmFull.Fn.M1097

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

def decode_aarch32_instrs_VCMLA_idx_T1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (rot : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int :=
    if ((S == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat Vm)
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let index : Int :=
    if ((S == 1#1) : Bool)
    then 0
    else (BitVec.toNat M)
  ArmFull.assert ((0 ≤b m) && ((m ≤b 31) && ((esize == 16) || (esize == 32)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46756.64-46756.65"
  (execute_aarch32_instrs_VCMLA_idx_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCADD_A1enc_A_txt (rot : (BitVec 1)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46829.41-46829.42"
  (execute_aarch32_instrs_VCADD_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCADD_T1enc_A_txt (rot : (BitVec 1)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46868.41-46868.42"
  (execute_aarch32_instrs_VCADD_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VFMAL_A1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat (Vm +++ M))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && (m ≤b 31)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46936.64-46936.65"
  (execute_aarch32_instrs_VFMAL_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) sub_op)


def decode_aarch32_instrs_VFMAL_T1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat (Vm +++ M))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && (m ≤b 31)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46972.64-46972.65"
  (execute_aarch32_instrs_VFMAL_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) sub_op)


def decode_aarch32_instrs_VFMAL_i_A1enc_A_txt (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
    else (BitVec.toNat ((Sail.BitVec.extractLsb Vm 2 0) +++ M))
  let index : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
    else (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)])))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:47039.89-47039.90"
  (execute_aarch32_instrs_VFMAL_i_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (index))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) sub_op)


def decode_aarch32_instrs_VFMAL_i_T1enc_A_txt (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
    else (BitVec.toNat ((Sail.BitVec.extractLsb Vm 2 0) +++ M))
  let index : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
    else (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)])))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:47076.89-47076.90"
  (execute_aarch32_instrs_VFMAL_i_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (index))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) sub_op)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMMLA_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let op1 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let acc ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (BFMatMulAdd (k_N := 128) acc op1 op2) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__0)


def decode_aarch32_instrs_VCVT_A1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VCVT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)))


def decode_aarch32_instrs_VCVT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VCVT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)))


def decode_aarch32_instrs_VCVTB_bf16_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:47410.29-47410.30"
      let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTB_bf16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VCVTB_bf16_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTB_bf16_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VCVTT_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:47467.29-47467.30"
      let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VCVTT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (Vd +++ D))
      let m : Int := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_VFMA_bf_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let sel : Int := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bf_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel)))


def decode_aarch32_instrs_VFMA_bf_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let sel : Int := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bf_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel)))


def decode_aarch32_instrs_VFMA_bfs_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             Vn 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
  let i : Int := (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let sel : Int := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bfs_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (sel)))


def decode_aarch32_instrs_VFMA_bfs_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             Vn 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
  let i : Int := (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let sel : Int := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bfs_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (sel)))


def decode_bfcvt_float_aarch64_instrs_vector_cvt_bf16_scalar (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_cvt_bf16_scalar (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)))


def decode_bfcvtn_advsimd_aarch64_instrs_vector_cvt_bf16_vector (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let part : Int := (BitVec.toNat Q)
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 64 16)))
  (execute_aarch64_instrs_vector_cvt_bf16_vector (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)))


def decode_bfdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_bfdot (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (M +++ Rm))
  let d : Int := (BitVec.toNat Rd)
  let i : Int := (BitVec.toNat (H +++ L))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_bfdot (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_bfdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_bfdot (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_bfdot (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_bfmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_bf16_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (0#1 +++ Rm))
  let d : Int := (BitVec.toNat Rd)
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let sel : Int := (BitVec.toNat Q)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_bf16_long
    (Sail.Int.toNatChecked (d)) elements (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel)))


def decode_bfmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_acc_bf16_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let sel : Int := (BitVec.toNat Q)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_acc_bf16_long
    (Sail.Int.toNatChecked (d)) elements (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (sel)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_bfmmla (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let op1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let acc ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (BFMatMulAdd (k_N := 128) acc op1 op2) ) : SailM (BitVec 128) )
  (V_set d 128 w__0)


def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let abs : Bool := true
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let abs : Bool := true
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let abs : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let abs : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fabs_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := 16
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize : Int := esize
  let fpop ← (( do (undefined_FPUnaryOp (← occLabel 4107) ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match opc with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) fpop (Sail.Int.toNatChecked (n)))


def decode_fmov_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := 16
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize : Int := esize
  let fpop ← (( do (undefined_FPUnaryOp (← occLabel 4108) ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match opc with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) fpop (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
