module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0884 set_option backward.proofsInPublic true @[expose] public section

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

def decode_fcsel_float_aarch64_instrs_float_move_fp_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ())))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let datasize : Int := datasize
  let condition : (BitVec 4) := cond
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_float_move_fp_select condition (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: datasize : Nat, rd : Nat, 0 ≤ rd ∧
  rd ≤ 31 ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_vector_fp16_movi (datasize : Nat) (imm : (BitVec datasize)) (rd : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  (V_set rd datasize (Sail.BitVec.castWidth imm))


def decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm (Rd : (BitVec 5)) (imm8 : (BitVec 8)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ())))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let datasize : Int := datasize
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (VFPExpandImm imm8 (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_float_move_fp_imm (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm))


/-- Type quantifiers: d : Nat, dst_index : Int, esize : Nat, idxdsize : Nat, n : Nat, src_index :
  Int, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64, 128, 256] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_insert (d : Nat) (dst_index : Int) (esize : Nat) (idxdsize : Nat) (n : Nat) (src_index : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let result ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand src_index esize)) ) : SailM
    (BitVec esize) )
  let w__1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result dst_index esize (Sail.BitVec.castWidth w__0))) )
    : SailM (BitVec 128) )
  let result := (w__1 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, index : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64, 128, 256] ∧ datasize = 128 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_insert (d : Nat) (datasize : Nat) (esize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:22661.48-22661.49"
  let element ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n esize)) ) : SailM (BitVec esize) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let w__0 ← (( do (Elem_set result index esize (Sail.BitVec.castWidth element)) ) : SailM
    (BitVec datasize) )
  let result := (w__0 : (BitVec datasize))
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4647)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4648)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4649)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4650)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, product, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, product, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, product, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let product : (BitVec esize) :=
            (Sail.BitVec.castWidth (integer_subrange
              ((BitVec.toNat element1) *i (BitVec.toNat element2)) (esize -i 1) 0))
          let result ← (( do
            if (sub_op : Bool)
            then
              (do
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth (w__2 - product))))
            else
              (do
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth (w__4 + product)))) ) : SailM
            (BitVec datasize) )
          (pure ((element1, element2, product, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4651)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4652) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4653)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 : Int := (BitVec.toNat w__0)
  let (element1, product, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, product, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, product, result) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toNat w__1) : Int)
          let product : (BitVec esize) :=
            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2) (esize -i 1) 0))
          let result ← (( do
            if (sub_op : Bool)
            then
              (do
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth (w__2 - product))))
            else
              (do
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth (w__4 + product)))) ) : SailM
            (BitVec datasize) )
          (pure ((element1, product, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_poly
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (poly : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4664)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4665)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4666)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4667)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, product, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, product, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, product, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let product : (BitVec esize) :=
            if (poly : Bool)
            then
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb (PolynomialMult element1 element2)
                (Sail.Int.toNatChecked ((esize -i 1))) 0))
            else
              (Sail.BitVec.castWidth (integer_subrange
                ((BitVec.toNat element1) *i (BitVec.toNat element2)) (esize -i 1) 0))
          let w__2 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth product)) ) : SailM
            (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element1, element2, product, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4668)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4669) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4670)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 : Int := (BitVec.toNat w__0)
  let (element1, product, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, product, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, product, result) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toNat w__1) : Int)
          let product : (BitVec esize) :=
            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2) (esize -i 1) 0))
          let w__2 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth product)) ) : SailM
            (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element1, product, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 8 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_not (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4673)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4674)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let w__1 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (Complement.complement element))) ) :
            SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part :
  Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4675)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4676)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4677)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let w__2 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (PolynomialMult element1 element2))) ) : SailM
            (BitVec (2 * datasize)) )
          let result := (w__2 : (BitVec (2 * datasize)))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


def decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3_rax1 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 8 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_rbit (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4683)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4684)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let rev ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4685)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result, rev) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := (element, result, rev)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, rev) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let rev ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := (Sail.Int.toNatChecked ((esize -i 1)))
            (do
              let mut loop_vars_1 := rev
              for i in [loop_i_lower:loop_i_upper:1]i do
                let rev := loop_vars_1
                loop_vars_1 :=
                  (BitVec.update rev (Sail.Int.toNatChecked (((esize -i 1) -i i)))
                    (Bit
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access element
                          (Sail.Int.toNatChecked (i)))]))))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          let w__1 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth rev)) ) : SailM
            (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((element, result, rev)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize) × (BitVec esize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: containers : Int, d : Nat, datasize : Nat, elements_per_container : Int, esize
  : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_rev (containers : Int) (d : Nat) (datasize : Nat) (elements_per_container : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4737)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element : Int := 0
  let rev_element ← (( do (undefined_int_at (← occLabel 4738) ()) ) : SailM Int )
  let (element, result, rev_element) ← (( do
    let loop_c_lower : Nat := 0
    let loop_c_upper : Int := (containers -i 1)
    (do
      let mut loop_vars := (element, result, rev_element)
      for c in [loop_c_lower:loop_c_upper:1]i do
        let (element, result, rev_element) := loop_vars
        loop_vars ← do
          let rev_element : Int := ((element +i elements_per_container) -i 1)
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements_per_container -i 1)
          (do
            let mut loop_vars_1 := (element, result, rev_element)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (element, result, rev_element) := loop_vars_1
              loop_vars_1 ← do
                let rev_element : Int := rev_element
                let element : Int := element
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand element esize))
                  ) : SailM (BitVec esize) )
                let w__1 ← (( do (Elem_set result rev_element esize (Sail.BitVec.castWidth w__0))
                  ) : SailM (BitVec datasize) )
                let result := (w__1 : (BitVec datasize))
                let element : Int := (element +i 1)
                let rev_element : Int := (rev_element -i 1)
                (pure ((element, result, rev_element)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Int) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, k_round
  : Bool, shift : Int, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_narrow_logical (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (round : Bool) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((datasize *i 2))))) ) : SailM
    (BitVec (datasize * 2)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4740)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4741) ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let w__1 ← (( do (RShr (BitVec.toNat w__0) shift round) ) : SailM Int )
          let element : Int := (w__1 : Int)
          let w__2 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange element (esize -i 1) 0))) ) : SailM
            (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize)) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_accumulate : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff (accumulate : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4742) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4743) ()) ) : SailM Int )
  let absdiff ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4744)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result ← (( do
    if (accumulate : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read d datasize)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := datasize))))) ) : SailM (BitVec datasize) )
  let (absdiff, element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (absdiff, element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (absdiff, element1, element2, result) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__2 : Int)
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__4 : Int)
          let absdiff : (BitVec esize) :=
            (Sail.BitVec.castWidth (integer_subrange (Int.natAbs (element1 -i element2))
              (esize -i 1) 0))
          let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth (w__5 + absdiff))) ) :
            SailM (BitVec datasize) )
          let result := (w__6 : (BitVec datasize))
          (pure ((absdiff, element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × Int × Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_accumulate : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff (accumulate : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4745) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4746) ()) ) : SailM Int )
  let absdiff ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4747)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let result ← (( do
    if (accumulate : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked ((2 *i datasize))))))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((2 *i datasize)))))))) )
    : SailM (BitVec (2 * datasize)) )
  let (absdiff, element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (absdiff, element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (absdiff, element1, element2, result) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__2 : Int)
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__4 : Int)
          let absdiff : (BitVec (2 * esize)) :=
            (Sail.BitVec.castWidth (integer_subrange (Int.natAbs (element1 -i element2))
              ((2 *i esize) -i 1) 0))
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read result e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__6 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (w__5 + absdiff))) ) : SailM (BitVec (2 * datasize)) )
          let result := (w__6 : (BitVec (2 * datasize)))
          (pure ((absdiff, element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec (2 * esize)) × Int × Int × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


end ArmFull.Functions
