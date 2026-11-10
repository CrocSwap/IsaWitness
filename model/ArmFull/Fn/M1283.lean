import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0175
import ArmFull.Fn.M1177
import ArmFull.Fn.M1178

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

def decode_aarch32_instrs_LDRSHT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:6619.29-6619.30"
      let m ← (( do (undefined_int_at (← occLabel 3084) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3085) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3086) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      (execute_aarch32_instrs_LDRSHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSHT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:6655.29-6655.30"
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3087) 32) ) : SailM (BitVec 32) )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      (execute_aarch32_instrs_LDRSHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRSHT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3088) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3089) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3090) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRSH (literal)"))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRSHT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:6750.29-6750.30"
      let m ← (( do (undefined_int_at (← occLabel 3091) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3092) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3093) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      (execute_aarch32_instrs_LDRT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:6785.29-6785.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3094) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3095) ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3096) 32) ) : SailM (BitVec 32) )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LDRT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3097) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3098) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3099) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDR (literal)"))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_MCR_A1enc_A_txt (cond : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7065.29-7065.30"
      let t : Int := (BitVec.toNat Rt)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MCR_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_MCR_T1enc_A_txt (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MCR_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_POP_T1enc_A_txt (P : (BitVec 1)) (register_list : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let registers : (BitVec 16) := ((P +++ 0b0000000#7) +++ register_list)
      let UnalignedAllowed : Bool := false
      if (((BitCount registers) <b 1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_POP_Op_A_txt UnalignedAllowed registers))
  else (pure (()))


def decode_aarch32_instrs_PUSH_T1enc_A_txt (M : (BitVec 1)) (register_list : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let registers : (BitVec 16) := (((0#1 +++ M) +++ 0b000000#6) +++ register_list)
      let UnalignedAllowed : Bool := false
      if (((BitCount registers) <b 1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_PUSH_Op_A_txt UnalignedAllowed registers))
  else (pure (()))


def decode_aarch32_instrs_STM_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:13454.29-13454.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STM_T1enc_A_txt (Rn : (BitVec 3)) (register_list : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := (0b00000000#8 +++ register_list)
      let wback : Bool := true
      if (((BitCount registers) <b 1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STM_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 13)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STMDA_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:13560.29-13560.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STMDA_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STMDB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:13610.29-13610.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STMDB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STMDB_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 13)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STMDB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STMIB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:13694.29-13694.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STMIB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:13737.29-13737.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "STRBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRB_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm5 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_STRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "STRBT"))
      else (pure (()))
      if (((Rn == 0b1111#4) || ((P == 0#1) && (W == 0#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:13898.29-13898.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3229) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3230) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "STRBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3231) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3232) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_STRB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRB_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3233) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3234) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_STRBT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:14027.29-14027.30"
      let m ← (( do (undefined_int_at (← occLabel 3235) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3236) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3237) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      (execute_aarch32_instrs_STRBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STRBT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:14062.29-14062.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3238) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3239) ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3240) 32) ) : SailM (BitVec 32) )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_STRBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STRBT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3241) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3242) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3243) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STRD_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:14164.29-14164.30"
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && (((n == 15) || (n == t)) || (n == t2))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((t2 == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STRD_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) wback))
  else (pure (()))


end ArmFull.Functions
