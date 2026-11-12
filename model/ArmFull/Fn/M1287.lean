import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0124
import ArmFull.Fn.M0166
import ArmFull.Fn.M1179
import ArmFull.Fn.M1180

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

def decode_aarch32_instrs_VLD3_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let inc_name : Int := 1
      let inc_name ← (( do
        match itype with
        | 0b0100 => (pure (1))
        | 0b0101 => (pure (2))
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name : Int := inc_name
      if (((size == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 1)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 0)])) == 0#1) : Bool)
        then 1
        else 8
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLD3_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD3_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let inc_name : Int := 1
      let inc_name ← (( do
        match itype with
        | 0b0100 => (pure (1))
        | 0b0101 => (pure (2))
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name : Int := inc_name
      if (((size == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 1)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 0)])) == 0#1) : Bool)
        then 1
        else 8
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLD3_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)"))
      else (pure (()))
      let ebytes : Nat := 1
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name : Nat := 1
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 4
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLD4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)"))
      else (pure (()))
      let ebytes : Nat := 2
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 1)])) == 0#1) : Bool)
        then 1
        else 2
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 8
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLD4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)"))
      else (pure (()))
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 4
      let index : Int :=
        (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 3)])))
      let inc_name : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 2)])) == 0#1) : Bool)
        then 1
        else 2
      let alignment : Int :=
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat (Sail.BitVec.extractLsb index_align 1 0)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "sail-arm/instrs32.sail:26383.183-26383.184"
      (execute_aarch32_instrs_VLD4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)"))
      else (pure (()))
      let ebytes : Nat := 1
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name : Nat := 1
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 4
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLD4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)"))
      else (pure (()))
      let ebytes : Nat := 2
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 1)])) == 0#1) : Bool)
        then 1
        else 2
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 8
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLD4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)"))
      else (pure (()))
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 4
      let index : Int :=
        (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 3)])))
      let inc_name : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 2)])) == 0#1) : Bool)
        then 1
        else 2
      let alignment : Int :=
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat (Sail.BitVec.extractLsb index_align 1 0)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "sail-arm/instrs32.sail:26502.183-26502.184"
      (execute_aarch32_instrs_VLD4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_a_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) && (a == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Int := 1
      let alignment ← (( do (undefined_int_at (← occLabel 3448) ()) ) : SailM Int )
      let (alignment, ebytes) : (Int × Int) :=
        if ((size == 0b11#2) : Bool)
        then
          (let ebytes : Int := 4
          let alignment : Int := 16
          (alignment, ebytes))
        else
          (let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
          let alignment : Int :=
            if ((size == 0b10#2) : Bool)
            then
              (if ((a == 0#1) : Bool)
              then 1
              else 8)
            else
              (if ((a == 0#1) : Bool)
              then 1
              else (4 *i ebytes))
          (alignment, ebytes))
      let ebytes : Int := ebytes
      let alignment : Int := alignment
      let inc_name : Int :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let alignment : Int := alignment
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "sail-arm/instrs32.sail:26586.149-26586.150"
      (execute_aarch32_instrs_VLD4_a_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 (Sail.Int.toNatChecked (ebytes))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_a_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) && (a == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Int := 1
      let alignment ← (( do (undefined_int_at (← occLabel 3449) ()) ) : SailM Int )
      let (alignment, ebytes) : (Int × Int) :=
        if ((size == 0b11#2) : Bool)
        then
          (let ebytes : Int := 4
          let alignment : Int := 16
          (alignment, ebytes))
        else
          (let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
          let alignment : Int :=
            if ((size == 0b10#2) : Bool)
            then
              (if ((a == 0#1) : Bool)
              then 1
              else 8)
            else
              (if ((a == 0#1) : Bool)
              then 1
              else (4 *i ebytes))
          (alignment, ebytes))
      let ebytes : Int := ebytes
      let alignment : Int := alignment
      let inc_name : Int :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let alignment : Int := alignment
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "sail-arm/instrs32.sail:26639.149-26639.150"
      (execute_aarch32_instrs_VLD4_a_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 (Sail.Int.toNatChecked (ebytes))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let inc_name : Int := 1
      let inc_name ← (( do
        match itype with
        | 0b0000 => (pure (1))
        | 0b0001 => (pure (2))
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name : Int := inc_name
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "sail-arm/instrs32.sail:26725.149-26725.150"
      (execute_aarch32_instrs_VLD4_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLD4_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let inc_name : Int := 1
      let inc_name ← (( do
        match itype with
        | 0b0000 => (pure (1))
        | 0b0001 => (pure (2))
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name : Int := inc_name
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let d3 : Int := (d2 +i inc_name)
      let d4 : Int := (d3 +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "sail-arm/instrs32.sail:26777.149-26777.150"
      (execute_aarch32_instrs_VLD4_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VLDM_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:26827.29-26827.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VLDR"))
      else (pure (()))
      if (((P == U) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let single_regs : Bool := false
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs : Int := (Int.ediv (BitVec.toNat imm8) 2)
      let w__3 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          if (wback : Bool)
          then (pure true)
          else
            (do
              let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
              (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((regs == 0) || (regs >b 16)) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 0)])) == 1#1) && ((d +i regs) >b 16)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLDM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VLDM_A2enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:26875.29-26875.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VLDR"))
      else (pure (()))
      if (((P == U) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let single_regs : Bool := true
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d : Int := (BitVec.toNat (Vd +++ D))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs : Int := (BitVec.toNat imm8)
      let w__3 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          if (wback : Bool)
          then (pure true)
          else
            (do
              let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
              (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((regs == 0) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLDM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VLDM_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VLDR"))
      else (pure (()))
      if (((P == U) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let single_regs : Bool := false
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs : Int := (Int.ediv (BitVec.toNat imm8) 2)
      let w__3 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          if (wback : Bool)
          then (pure true)
          else
            (do
              let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
              (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((regs == 0) || (regs >b 16)) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 0)])) == 1#1) && ((d +i regs) >b 16)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLDM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VLDM_T2enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VLDR"))
      else (pure (()))
      if (((P == U) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let single_regs : Bool := true
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d : Int := (BitVec.toNat (Vd +++ D))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs : Int := (BitVec.toNat imm8)
      let w__3 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          if (wback : Bool)
          then (pure true)
          else
            (do
              let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
              (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((regs == 0) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VLDM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


end ArmFull.Functions
