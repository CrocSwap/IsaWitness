import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0175
import ArmFull.Fn.M1010
import ArmFull.Fn.M1011

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

def decode_aarch32_instrs_VQMOVN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((op == 0b00#2) : Bool)
      then sailThrow ((Error_See "VMOVN"))
      else (pure (()))
      if (((size == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let src_unsigned : Bool := (op == 0b11#2)
      let dest_unsigned : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQMOVN_Op_A_txt (Sail.Int.toNatChecked (d)) dest_unsigned elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) src_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VQMOVN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((op == 0b00#2) : Bool)
      then sailThrow ((Error_See "VMOVN"))
      else (pure (()))
      if (((size == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let src_unsigned : Bool := (op == 0b11#2)
      let dest_unsigned : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQMOVN_Op_A_txt (Sail.Int.toNatChecked (d)) dest_unsigned elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) src_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VQNEG_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQNEG_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VQNEG_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQNEG_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VQRDMULH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3653) ()) ) : SailM Int )
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let scalar_form : Bool := false
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQRDMULH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((size == 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3654) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3655) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3656) ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Int := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int :=
            (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Int := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m : Int := m
      let index : Int := index
      let esize : Int := esize
      let elements : Int := elements
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:33186.135-33186.136"
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQRDMULH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3657) ()) ) : SailM Int )
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let scalar_form : Bool := false
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQRDMULH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((size == 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3658) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3659) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3660) ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Int := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int :=
            (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Int := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m : Int := m
      let index : Int := index
      let esize : Int := esize
      let elements : Int := elements
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:33279.135-33279.136"
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQRDMLAH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int_at (← occLabel 3666) ()) ) : SailM Int )
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := index
  let add : Bool := true
  let scalar_form : Bool := false
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLAH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_See "Related encodings"))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let add : Bool := true
  let scalar_form : Bool := true
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Int := 8
  let elements ← (( do (undefined_int_at (← occLabel 3667) ()) ) : SailM Int )
  let m ← (( do (undefined_int_at (← occLabel 3668) ()) ) : SailM Int )
  let index ← (( do (undefined_int_at (← occLabel 3669) ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Int := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int :=
        (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Int := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m : Int := m
  let index : Int := index
  let esize : Int := esize
  let elements : Int := elements
  ArmFull.assert ((0 ≤b m) && (m ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:33410.43-33410.44"
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLAH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int_at (← occLabel 3670) ()) ) : SailM Int )
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := index
  let add : Bool := true
  let scalar_form : Bool := false
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLAH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_See "Related encodings"))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let add : Bool := true
  let scalar_form : Bool := true
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Int := 8
  let elements ← (( do (undefined_int_at (← occLabel 3671) ()) ) : SailM Int )
  let m ← (( do (undefined_int_at (← occLabel 3672) ()) ) : SailM Int )
  let index ← (( do (undefined_int_at (← occLabel 3673) ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Int := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int :=
        (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Int := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m : Int := m
  let index : Int := index
  let esize : Int := esize
  let elements : Int := elements
  ArmFull.assert ((0 ≤b m) && (m ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:33511.43-33511.44"
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLSH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int_at (← occLabel 3679) ()) ) : SailM Int )
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := index
  let add : Bool := false
  let scalar_form : Bool := false
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLSH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_See "Related encodings"))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let add : Bool := false
  let scalar_form : Bool := true
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Int := 8
  let elements ← (( do (undefined_int_at (← occLabel 3680) ()) ) : SailM Int )
  let m ← (( do (undefined_int_at (← occLabel 3681) ()) ) : SailM Int )
  let index ← (( do (undefined_int_at (← occLabel 3682) ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Int := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int :=
        (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Int := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m : Int := m
  let index : Int := index
  let esize : Int := esize
  let elements : Int := elements
  ArmFull.assert ((0 ≤b m) && (m ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:33640.43-33640.44"
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLSH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int_at (← occLabel 3683) ()) ) : SailM Int )
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := index
  let add : Bool := false
  let scalar_form : Bool := false
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


def decode_aarch32_instrs_VQRDMLSH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveQRDMLAHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_See "Related encodings"))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let add : Bool := false
  let scalar_form : Bool := true
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Int := 8
  let m ← (( do (undefined_int_at (← occLabel 3684) ()) ) : SailM Int )
  let index ← (( do (undefined_int_at (← occLabel 3685) ()) ) : SailM Int )
  let elements ← (( do (undefined_int_at (← occLabel 3686) ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Int := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int :=
        (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Int := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m : Int := m
  let index : Int := index
  let esize : Int := esize
  let elements : Int := elements
  ArmFull.assert ((0 ≤b m) && (m ≤b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:33741.43-33741.44"
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) scalar_form)


end ArmFull.Functions
