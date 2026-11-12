import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0124
import ArmFull.Fn.M1012

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

def decode_aarch32_instrs_VREV16_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let container_size : Int := 16
      let container_size : Int :=
        match op with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size : Int := container_size
      let containers : Int := (Int.ediv 64 (Sail.Int.toNatChecked (container_size)))
      let elements_per_container : Int :=
        (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VREV16_Op_A_txt containers (Sail.Int.toNatChecked (d))
        elements_per_container (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VREV16_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let container_size : Int := 16
      let container_size : Int :=
        match op with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size : Int := container_size
      let containers : Int := (Int.ediv 64 (Sail.Int.toNatChecked (container_size)))
      let elements_per_container : Int :=
        (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VREV16_Op_A_txt containers (Sail.Int.toNatChecked (d))
        elements_per_container (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRHADD_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRHADD_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VRHADD_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRHADD_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VRSHL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vm 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSHL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VRSHL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vm 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSHL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VRSHR_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 8
      let elements : Int := 1
      let shift_amount ← (( do (undefined_int_at (← occLabel 3719) ()) ) : SailM Int )
      let b__1 := (L +++ imm6)
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__1 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (let esize : Int := 8
          let elements : Int := 8
          let shift_amount : Int := (16 -i (BitVec.toNat imm6))
          (elements, esize, shift_amount))
        else
          (let (elements, esize, shift_amount) : (Int × Int × Int) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 6 4)) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 16
              let elements : Int := 4
              let shift_amount : Int := (32 -i (BitVec.toNat imm6))
              (elements, esize, shift_amount))
            else
              (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 6 5)) == (0b01#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 32
                  let elements : Int := 2
                  let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                  (elements, esize, shift_amount))
                else
                  (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 6 6)) == (1#1 : (BitVec 1))) : Bool)
                    then
                      (let esize : Int := 64
                      let elements : Int := 1
                      let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                      (elements, esize, shift_amount))
                    else (elements, esize, shift_amount)
                  (elements, esize, shift_amount))
              (elements, esize, shift_amount))
          (elements, esize, shift_amount))
      let shift_amount : Int := shift_amount
      let esize : Int := esize
      let elements : Int := elements
      let is_unsigned : Bool := (U == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 8 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 16 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 16 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 32 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 32 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 64 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 64 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs32.sail:35204.26-35204.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VRSHR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 8
      let elements : Int := 1
      let shift_amount ← (( do (undefined_int_at (← occLabel 3720) ()) ) : SailM Int )
      let b__1 := (L +++ imm6)
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__1 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (let esize : Int := 8
          let elements : Int := 8
          let shift_amount : Int := (16 -i (BitVec.toNat imm6))
          (elements, esize, shift_amount))
        else
          (let (elements, esize, shift_amount) : (Int × Int × Int) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 6 4)) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 16
              let elements : Int := 4
              let shift_amount : Int := (32 -i (BitVec.toNat imm6))
              (elements, esize, shift_amount))
            else
              (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 6 5)) == (0b01#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 32
                  let elements : Int := 2
                  let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                  (elements, esize, shift_amount))
                else
                  (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 6 6)) == (1#1 : (BitVec 1))) : Bool)
                    then
                      (let esize : Int := 64
                      let elements : Int := 1
                      let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                      (elements, esize, shift_amount))
                    else (elements, esize, shift_amount)
                  (elements, esize, shift_amount))
              (elements, esize, shift_amount))
          (elements, esize, shift_amount))
      let shift_amount : Int := shift_amount
      let esize : Int := esize
      let elements : Int := elements
      let is_unsigned : Bool := (U == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 8 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 16 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 16 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 32 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 32 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 64 =>
        (do
          (execute_aarch32_instrs_VRSHR_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 64 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs32.sail:35284.26-35284.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VRSHRN_A1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := imm6
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 8
      let elements : Int := 2
      let shift_amount ← (( do (undefined_int_at (← occLabel 3722) ()) ) : SailM Int )
      let b__1 := imm6
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 5 3)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (let esize : Int := 8
          let elements : Int := 8
          let shift_amount : Int := (16 -i (BitVec.toNat imm6))
          (elements, esize, shift_amount))
        else
          (let (elements, esize, shift_amount) : (Int × Int × Int) :=
            if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 5 4)) == (0b01#2 : (BitVec 2))) : Bool)
            then
              (let esize : Int := 16
              let elements : Int := 4
              let shift_amount : Int := (32 -i (BitVec.toNat imm6))
              (elements, esize, shift_amount))
            else
              (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 5 5)) == (1#1 : (BitVec 1))) : Bool)
                then
                  (let esize : Int := 32
                  let elements : Int := 2
                  let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                  (elements, esize, shift_amount))
                else (elements, esize, shift_amount)
              (elements, esize, shift_amount))
          (elements, esize, shift_amount))
      let shift_amount : Int := shift_amount
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VRSHRN_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) shift_amount))
  else (pure (()))


def decode_aarch32_instrs_VRSHRN_T1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := imm6
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 8
      let elements : Int := 2
      let shift_amount ← (( do (undefined_int_at (← occLabel 3723) ()) ) : SailM Int )
      let b__1 := imm6
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 5 3)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (let esize : Int := 8
          let elements : Int := 8
          let shift_amount : Int := (16 -i (BitVec.toNat imm6))
          (elements, esize, shift_amount))
        else
          (let (elements, esize, shift_amount) : (Int × Int × Int) :=
            if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 5 4)) == (0b01#2 : (BitVec 2))) : Bool)
            then
              (let esize : Int := 16
              let elements : Int := 4
              let shift_amount : Int := (32 -i (BitVec.toNat imm6))
              (elements, esize, shift_amount))
            else
              (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 5 5)) == (1#1 : (BitVec 1))) : Bool)
                then
                  (let esize : Int := 32
                  let elements : Int := 2
                  let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                  (elements, esize, shift_amount))
                else (elements, esize, shift_amount)
              (elements, esize, shift_amount))
          (elements, esize, shift_amount))
      let shift_amount : Int := shift_amount
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VRSHRN_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) shift_amount))
  else (pure (()))


def decode_aarch32_instrs_VRSRA_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 8
      let elements : Int := 1
      let shift_amount ← (( do (undefined_int_at (← occLabel 3725) ()) ) : SailM Int )
      let b__1 := (L +++ imm6)
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__1 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (let esize : Int := 8
          let elements : Int := 8
          let shift_amount : Int := (16 -i (BitVec.toNat imm6))
          (elements, esize, shift_amount))
        else
          (let (elements, esize, shift_amount) : (Int × Int × Int) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 6 4)) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 16
              let elements : Int := 4
              let shift_amount : Int := (32 -i (BitVec.toNat imm6))
              (elements, esize, shift_amount))
            else
              (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 6 5)) == (0b01#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 32
                  let elements : Int := 2
                  let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                  (elements, esize, shift_amount))
                else
                  (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 6 6)) == (1#1 : (BitVec 1))) : Bool)
                    then
                      (let esize : Int := 64
                      let elements : Int := 1
                      let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                      (elements, esize, shift_amount))
                    else (elements, esize, shift_amount)
                  (elements, esize, shift_amount))
              (elements, esize, shift_amount))
          (elements, esize, shift_amount))
      let shift_amount : Int := shift_amount
      let esize : Int := esize
      let elements : Int := elements
      let is_unsigned : Bool := (U == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 8 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 16 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 16 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 32 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 32 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 64 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 64 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs32.sail:35727.26-35727.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VRSRA_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 8
      let elements : Int := 1
      let shift_amount ← (( do (undefined_int_at (← occLabel 3726) ()) ) : SailM Int )
      let b__1 := (L +++ imm6)
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__1 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (let esize : Int := 8
          let elements : Int := 8
          let shift_amount : Int := (16 -i (BitVec.toNat imm6))
          (elements, esize, shift_amount))
        else
          (let (elements, esize, shift_amount) : (Int × Int × Int) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 6 4)) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 16
              let elements : Int := 4
              let shift_amount : Int := (32 -i (BitVec.toNat imm6))
              (elements, esize, shift_amount))
            else
              (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 6 5)) == (0b01#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 32
                  let elements : Int := 2
                  let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                  (elements, esize, shift_amount))
                else
                  (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 6 6)) == (1#1 : (BitVec 1))) : Bool)
                    then
                      (let esize : Int := 64
                      let elements : Int := 1
                      let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                      (elements, esize, shift_amount))
                    else (elements, esize, shift_amount)
                  (elements, esize, shift_amount))
              (elements, esize, shift_amount))
          (elements, esize, shift_amount))
      let shift_amount : Int := shift_amount
      let esize : Int := esize
      let elements : Int := elements
      let is_unsigned : Bool := (U == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 8 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 16 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 16 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 32 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 32 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | 64 =>
        (do
          (execute_aarch32_instrs_VRSRA_Op_A_txt (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (elements)) 64 (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (regs)) shift_amount is_unsigned))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs32.sail:35807.26-35807.27"
          throw Error.Exit))
  else (pure (()))


end ArmFull.Functions
