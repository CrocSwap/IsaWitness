import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0147
import ArmFull.Fn.M0180
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M1174
import ArmFull.Fn.M1188
import ArmFull.Fn.M1189

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

def decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpairpost (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_st2g_aarch64_instrs_integer_tags_mcsettagpair (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpairpost (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stg_aarch64_instrs_integer_tags_mcsettagpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpost (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stg_aarch64_instrs_integer_tags_mcsettagpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpost (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stg_aarch64_instrs_integer_tags_mcsettag (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpost (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let t2 : Int := (BitVec.toNat Xt2)
  let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Sail.Int.toNatChecked (n)) offset
    postindex (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) writeback)


def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let t2 : Int := (BitVec.toNat Xt2)
  let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Sail.Int.toNatChecked (n)) offset
    postindex (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) writeback)


def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapair (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let t2 : Int := (BitVec.toNat Xt2)
  let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Sail.Int.toNatChecked (n)) offset
    postindex (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) writeback)


def decode_stilp_aarch64_instrs_memory_ordered_pair_stilp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc2 : (BitVec 4)) (Rt2 : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let postindex : Bool := false
  let wback : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1)
  let offset ← (( do (undefined_int_at (← occLabel 5001) ()) ) : SailM Int )
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let memop ← (( do (undefined_MemOp (← occLabel 5002) ()) ) : SailM MemOp )
  let (memop, offset) : (MemOp × Int) :=
    if ((L == 1#1) : Bool)
    then
      (let memop : MemOp := MemOp_LOAD
      let offset : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1) : Bool)
        then (Int.shiftl 2 (Sail.Int.toNatChecked (scale)))
        else 0
      (memop, offset))
    else
      (let memop : MemOp := MemOp_STORE
      let offset : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1) : Bool)
        then ((Neg.neg 1) *i (Int.shiftl 2 (Sail.Int.toNatChecked (scale))))
        else 0
      (memop, offset))
  let offset : Int := offset
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:51080.113-51080.114"
        match c with
        | .Constraint_WBSUPPRESS =>
          (let wback : Bool := false
          (pure ((wb_unknown, wback))))
        | .Constraint_UNKNOWN =>
          (let wb_unknown : Bool := true
          (pure ((wb_unknown, wback))))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure ((wb_unknown, wback))))
        | _ => (pure ((wb_unknown, wback))))
    else (pure ((wb_unknown, wback))) ) : SailM (Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:51099.107-51099.108"
        match c with
        | .Constraint_NONE => (pure (false))
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:51118.84-51118.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "sail-arm/instrs64.sail:51132.44-51132.45"
  (execute_aarch64_instrs_memory_ordered_pair_stilp (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Sail.Int.toNatChecked (n))
    offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodatapre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Sail.Int.toNatChecked (n))
    offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodata (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Sail.Int.toNatChecked (n))
    offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Sail.Int.toNatChecked (n)) offset
    postindex (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodatapre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Sail.Int.toNatChecked (n)) offset
    postindex (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodata (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Sail.Int.toNatChecked (n)) offset
    postindex (Sail.Int.toNatChecked (t)) writeback zero_data)


def decode_stzgm_aarch64_instrs_integer_tags_mcsettagandzeroarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Xt)
  let n : Int := (BitVec.toNat Xn)
  (execute_aarch64_instrs_integer_tags_mcsettagandzeroarray (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADDV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5346.45-5346.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM (BitVec esize)
    )
  let w__2 ← (( do (ReducePredicated ReduceOp_FADD operand mask identity) ) : SailM (BitVec esize)
    )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5407.45-5407.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMAXNUM operand mask identity) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5468.45-5468.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMINNUM operand mask identity) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5529.45-5529.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMAX operand mask identity) ) : SailM (BitVec esize)
    )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5590.45-5590.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMIN operand mask identity) ) : SailM (BitVec esize)
    )
  (V_set d esize (Sail.BitVec.castWidth w__2))


def decode_FADDQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  match VL with
  | 128 =>
    (do
      (execute_FADDQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FADDQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FADDQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FADDQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FADDQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMAXNMQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  match VL with
  | 128 =>
    (do
      (execute_FMAXNMQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMAXNMQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMAXNMQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMAXNMQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMAXNMQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMINNMQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  match VL with
  | 128 =>
    (do
      (execute_FMINNMQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMINNMQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMINNMQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMINNMQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMINNMQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMAXQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  match VL with
  | 128 =>
    (do
      (execute_FMAXQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMAXQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMAXQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMAXQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMAXQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMINQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  match VL with
  | 128 =>
    (do
      (execute_FMINQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMINQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMINQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMINQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMINQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
