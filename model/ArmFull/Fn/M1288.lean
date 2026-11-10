import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0086
import ArmFull.Fn.M0124
import ArmFull.Fn.M0175
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

def decode_aarch32_instrs_VLDR_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:27036.29-27036.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let add : Bool := (U == 1#1)
      let imm32 : (BitVec 32) :=
        if ((esize == 16) : Bool)
        then (Sail.BitVec.zeroExtend (imm8 +++ 0#1) 32)
        else (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3454) 0 31))) ) :
        SailM Nat )
      let d : Nat :=
        match size with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d : Int := d
      let n : Int := (BitVec.toNat Rn)
      (execute_aarch32_instrs_VLDR_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VLDR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let add : Bool := (U == 1#1)
      let imm32 : (BitVec 32) :=
        if ((esize == 16) : Bool)
        then (Sail.BitVec.zeroExtend (imm8 +++ 0#1) 32)
        else (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3455) 0 31))) ) :
        SailM Nat )
      let d : Nat :=
        match size with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d : Int := d
      let n : Int := (BitVec.toNat Rn)
      (execute_aarch32_instrs_VLDR_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VST1_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) != 0#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 1
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let alignment : Nat := 1
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment (Sail.Int.toNatChecked (d)) ebytes
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 1)])) != 0#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 2
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 2
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST1_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 2)])) != 0#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) != 0b00#2) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               index_align 1 0)) != 0b11#2)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 4
      let index : Int :=
        (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 3)])))
      let alignment : Int :=
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) == 0b00#2) : Bool)
        then 1
        else 4
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST1_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) != 0#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 1
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let alignment : Nat := 1
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment (Sail.Int.toNatChecked (d)) ebytes
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 1)])) != 0#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 2
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 2
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST1_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 2)])) != 0#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) != 0b00#2) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               index_align 1 0)) != 0b11#2)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 4
      let index : Int :=
        (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 3)])))
      let alignment : Int :=
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb index_align 1 0)) == 0b00#2) : Bool)
        then 1
        else 4
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST1_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 1
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 1)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37615.173-37615.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 2
      if ((align == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37652.173-37652.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 3
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 1)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37689.173-37689.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_A4enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 4
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37723.173-37723.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 1
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 1)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37760.173-37760.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 2
      if ((align == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37797.173-37797.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 3
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access align 1)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37834.173-37834.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST1_m_T4enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let regs : Nat := 4
      let alignment : Int :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
      let elements : Int := (Int.ediv 8 (Sail.Int.toNatChecked (ebytes)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      ArmFull.assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:37868.173-37868.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index regs wback))
  else (pure (()))


def decode_aarch32_instrs_VST2_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 1
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name : Nat := 1
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 2
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST2_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST2_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
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
        else 4
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST2_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST2_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 1)])) != 0#1) : Bool)
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
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 8
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST2_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST2_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ebytes : Nat := 1
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name : Nat := 1
      let alignment : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access index_align 0)])) == 0#1) : Bool)
        then 1
        else 2
      let d : Int := (BitVec.toNat (D +++ Vd))
      let d2 : Int := (d +i inc_name)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VST2_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


end ArmFull.Functions
