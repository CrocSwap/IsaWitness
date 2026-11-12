import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0124
import ArmFull.Fn.M1010

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

def decode_aarch32_instrs_VQDMLAL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3599) ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLAL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3600) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3601) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3602) ()) ) : SailM Int )
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "sail-arm/instrs32.sail:32155.117-32155.118"
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLAL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3603) ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLAL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3604) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3605) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3606) ()) ) : SailM Int )
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "sail-arm/instrs32.sail:32245.117-32245.118"
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLSL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3613) ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLSL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3614) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3615) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3616) ()) ) : SailM Int )
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "sail-arm/instrs32.sail:32377.117-32377.118"
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLSL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3617) ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMLSL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3618) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3619) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3620) ()) ) : SailM Int )
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "sail-arm/instrs32.sail:32467.117-32467.118"
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3625) ()) ) : SailM Int )
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
      (execute_aarch32_instrs_VQDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let elements ← (( do (undefined_int_at (← occLabel 3626) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3627) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3628) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "sail-arm/instrs32.sail:32590.135-32590.136"
      (execute_aarch32_instrs_VQDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3629) ()) ) : SailM Int )
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
      (execute_aarch32_instrs_VQDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let elements ← (( do (undefined_int_at (← occLabel 3630) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3631) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3632) ()) ) : SailM Int )
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
      ArmFull.assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "sail-arm/instrs32.sail:32683.135-32683.136"
      (execute_aarch32_instrs_VQDMULH_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3637) ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let scalar_form : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      (execute_aarch32_instrs_VQDMULL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3638) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3639) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3640) ()) ) : SailM Int )
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "sail-arm/instrs32.sail:32798.117-32798.118"
      (execute_aarch32_instrs_VQDMULL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let index ← (( do (undefined_int_at (← occLabel 3641) ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Int := index
      let scalar_form : Bool := false
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      (execute_aarch32_instrs_VQDMULL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


def decode_aarch32_instrs_VQDMULL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let scalar_form : Bool := true
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let esize : Int := 8
      let elements ← (( do (undefined_int_at (← occLabel 3642) ()) ) : SailM Int )
      let m ← (( do (undefined_int_at (← occLabel 3643) ()) ) : SailM Int )
      let index ← (( do (undefined_int_at (← occLabel 3644) ()) ) : SailM Int )
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "sail-arm/instrs32.sail:32884.117-32884.118"
      (execute_aarch32_instrs_VQDMULL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) scalar_form))
  else (pure (()))


end ArmFull.Functions
