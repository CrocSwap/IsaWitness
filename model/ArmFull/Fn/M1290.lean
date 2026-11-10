import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0166
import ArmFull.Fn.M0175
import ArmFull.Fn.M1181
import ArmFull.Fn.M1182

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

def decode_aarch32_instrs_VST4_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b01#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
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
      (execute_aarch32_instrs_VST4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST4_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:38974.183-38974.184"
      (execute_aarch32_instrs_VST4_1_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 ebytes (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST4_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let inc_name : Int := 1
      let inc_name ← (( do
        match itype with
        | 0b0000 => (pure (1))
        | 0b0001 => (pure (2))
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name : Int := inc_name
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:39055.149-39055.150"
      (execute_aarch32_instrs_VST4_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VST4_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let inc_name : Int := 1
      let inc_name ← (( do
        match itype with
        | 0b0000 => (pure (1))
        | 0b0001 => (pure (2))
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name : Int := inc_name
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
      ArmFull.assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:39107.149-39107.150"
      (execute_aarch32_instrs_VST4_m_Op_A_txt (Sail.Int.toNatChecked (alignment))
        (Sail.Int.toNatChecked (d)) d2 d3 d4 (Sail.Int.toNatChecked (ebytes)) elements
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) register_index wback))
  else (pure (()))


def decode_aarch32_instrs_VSTM_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:39157.29-39157.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VSTR"))
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VSTM_A2enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:39205.29-39205.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VSTR"))
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VSTM_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VSTR"))
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VSTM_T2enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "VSTR"))
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) regs single_regs wback))
  else (pure (()))


def decode_aarch32_instrs_VSTR_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:39367.29-39367.30"
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
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3754) 0 31))) ) :
        SailM Nat )
      let d : Nat :=
        match size with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d : Int := d
      let n : Int := (BitVec.toNat Rn)
      let w__2 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
            (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d : Int := d
      (execute_aarch32_instrs_VSTR_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VSTR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
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
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3755) 0 31))) ) :
        SailM Nat )
      let d : Nat :=
        match size with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d : Int := d
      let n : Int := (BitVec.toNat Rn)
      let w__4 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          (do
            let w__3 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
            (pure (((bne w__3 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d : Int := d
      (execute_aarch32_instrs_VSTR_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_LDM_e_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 15)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:40995.29-40995.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 15) := register_list
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_e_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) registers
        wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_LDM_u_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 15)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:41055.29-41055.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 15) := register_list
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_u_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) registers
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_RFE_A1enc_AS_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) wback
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_RFE_T1enc_AS_txt (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := false
      let wordhigher : Bool := false
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) wback
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_RFE_T2enc_AS_txt (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := true
      let wordhigher : Bool := false
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) wback
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_SRS_A1enc_AS_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      (execute_aarch32_instrs_SRS_OpA_AS_txt increment_name mode wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_SRS_T1enc_AS_txt (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := false
      let wordhigher : Bool := false
      (execute_aarch32_instrs_SRS_OpT_AS_txt increment_name mode wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_SRS_T2enc_AS_txt (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := true
      let wordhigher : Bool := false
      (execute_aarch32_instrs_SRS_OpT_AS_txt increment_name mode wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_STM_u_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:41928.29-41928.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STM_u_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) registers
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_LDA_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:42802.29-42802.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDA_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDA_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDA_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


end ArmFull.Functions
