module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0885 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, part : Nat, shift : Nat, List.elem shift [8, 16, 32, 64] ∧
  List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_shift (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (shift : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4800)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element ← (( do (undefined_int_at (← occLabel 4801) ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element : Int := ((Int.shiftl w__1 shift) : Int)
          let w__2 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange element ((2 *i esize) -i 1) 0))) ) : SailM
            (BitVec (2 * datasize)) )
          let result := (w__2 : (BitVec (2 * datasize)))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4802)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4803) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4804) ()) ) : SailM Int )
  let diff ← (( do (undefined_int_at (← occLabel 4805) ()) ) : SailM Int )
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (diff, element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (diff, element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let diff : Int := (Int.shiftr (element1 -i element2) 1)
          let w__4 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange diff (esize -i 1) 0)))
            ) : SailM (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((diff, element1, element2, result)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Int, elements : Int, esize : Int, n : Nat, shift : Int, 0
  ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_insert_sisd (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:44507.56-44507.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (datasize))))
    ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4806)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  ArmFull.assert (esize ≥b 0) "sail-inputs/15-instrs64.sail:44511.34-44511.35"
  let mask : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth ((Ones (n := (Sail.Int.toNatChecked (esize)))) <<< shift))
  let shifted ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4807)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let (result, shifted) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (result, shifted)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, shifted) := loop_vars
        loop_vars ← do
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || ((! (esize ≥b 0)) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)))))) "sail-inputs/15-instrs64.sail:44515.198-44515.199"
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          let shifted := ((w__0 <<< shift) : (BitVec (Sail.Int.toNatChecked (esize : Int))))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e (Sail.Int.toNatChecked (esize)))) )
            : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          let w__2 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked (esize))
              (Sail.BitVec.castWidth ((w__1 &&& (Complement.complement mask)) ||| shifted))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
          let result := (w__2 : (BitVec (Sail.Int.toNatChecked (datasize : Int))))
          (pure ((result, shifted)))
      (pure loop_vars)) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (esize : Int))))
    )
  (V_set d (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth result))


def decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      let a : Int := (BitVec.toNat Ra)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 (Sail.Int.toNatChecked (a))
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      let i : Int := (BitVec.toNat imm2)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      let i : Int := (BitVec.toNat imm2)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      let i : Int := (BitVec.toNat imm2)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
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
      let i : Int := (BitVec.toNat imm2)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM4Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sm4_sm4enc (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n))))


def decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM4Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sm4_sm4enckey (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, k_minimum : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4821)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4822) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4823) ()) ) : SailM Int )
  let maxmin ← (( do (undefined_int_at (← occLabel 4824) ()) ) : SailM Int )
  let (element1, element2, maxmin, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, maxmin, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, maxmin, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let maxmin : Int :=
            if (minimum : Bool)
            then (Min.min element1 element2)
            else (Max.max element1 element2)
          let w__4 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange maxmin (esize -i 1) 0))) ) : SailM
            (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, maxmin, result)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, k_minimum : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4825)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  let element1 ← (( do (undefined_int_at (← occLabel 4826) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4827) ()) ) : SailM Int )
  let maxmin ← (( do (undefined_int_at (← occLabel 4828) ()) ) : SailM Int )
  let (element1, element2, maxmin, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, maxmin, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, maxmin, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read concat (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read concat ((2 *i e) +i 1) esize))
            ) : SailM (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let maxmin : Int :=
            if (minimum : Bool)
            then (Min.min element1 element2)
            else (Max.max element1 element2)
          let w__4 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange maxmin (esize -i 1) 0))) ) : SailM
            (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, maxmin, result)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_min
  : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_int_max (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (min : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4829) ()) ) : SailM Int )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand 0 esize)) ) : SailM
    (BitVec esize) )
  let maxmin ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
  let (element, maxmin) ← (( do
    let loop_e_lower : Nat := 1
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, maxmin)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, maxmin) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let element : Int := (w__2 : Int)
          let maxmin : Int :=
            if (min : Bool)
            then (Min.min maxmin element)
            else (Max.max maxmin element)
          (pure ((element, maxmin)))
      (pure loop_vars)) ) : SailM (Int × Int) )
  let maxmin : Int := maxmin
  (V_set d esize (Sail.BitVec.castWidth (integer_subrange maxmin (esize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4830)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4831) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4832) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4833)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let accum ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4834)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let (accum, element1, element2, product, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accum, element1, element2, product, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accum, element1, element2, product, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let product : (BitVec (2 * esize)) :=
            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0))
          let accum ← (( do
            if (sub_op : Bool)
            then
              (do
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let accum := ((w__4 - product) : (BitVec (2 * esize)))
                (pure (accum)))
            else
              (do
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let accum := ((w__5 + product) : (BitVec (2 * esize)))
                (pure (accum))) ) : SailM (BitVec (2 * esize)) )
          let w__6 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize))) (Sail.BitVec.castWidth accum))
            ) : SailM (BitVec (2 * datasize)) )
          let result := (w__6 : (BitVec (2 * datasize)))
          (pure ((accum, element1, element2, product, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (2 * esize)) × Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1]
  ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let operand3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4835)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4836) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4837)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
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
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__2 : Int)
          let product : (BitVec (2 * esize)) :=
            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0))
          let result ← (( do
            if (sub_op : Bool)
            then
              (do
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
                  (Sail.BitVec.castWidth (w__3 - product))))
            else
              (do
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
                  (Sail.BitVec.castWidth (w__5 + product)))) ) : SailM (BitVec (2 * datasize)) )
          (pure ((element1, product, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (2 * esize)) × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤
  n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (d : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let addend ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (MatMulAdd (k_N := 128) addend operand1 operand2 op1_unsigned op2_unsigned) ) :
    SailM (BitVec 128) )
  (V_set d 128 w__0)


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, idxdsize : Nat, index : Int, n : Nat, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_move_signed (d : Nat) (datasize : Nat) (esize : Nat) (idxdsize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  if ((index == 0) : Bool)
  then
    (do
      (CheckFPEnabled64 ()))
  else
    (do
      (CheckFPAdvSIMDEnabled64 ()))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand index esize)) ) : SailM
    (BitVec esize) )
  (X_set d datasize (Sail.BitVec.castWidth (sign_extend w__0 datasize)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4852)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4853) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4854) ()) ) : SailM Int )
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
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let w__4 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)))
            ) : SailM (BitVec (2 * datasize)) )
          let result := (w__4 : (BitVec (2 * datasize)))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


end ArmFull.Functions
