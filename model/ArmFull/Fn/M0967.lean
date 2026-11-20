module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0884
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

/-- Type quantifiers: k_acc : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned
  : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise (acc : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4748)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let sum ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4749)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let op1 ← (( do (undefined_int_at (← occLabel 4750) ()) ) : SailM Int )
  let op2 ← (( do (undefined_int_at (← occLabel 4751) ()) ) : SailM Int )
  let result ← (( do
    if (acc : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read d datasize)))
    else (pure (result)) ) : SailM (BitVec datasize) )
  let (op1, op2, result, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (op1, op2, result, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (op1, op2, result, sum) := loop_vars
        loop_vars ← do
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i e) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let op1 : Int := (w__2 : Int)
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i e) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
          let op2 : Int := (w__4 : Int)
          let sum : (BitVec (2 * esize)) :=
            (Sail.BitVec.castWidth (integer_subrange (op1 +i op2) ((2 *i esize) -i 1) 0))
          let result ← (( do
            if (acc : Bool)
            then
              (do
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read result e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
                  (Sail.BitVec.castWidth (w__5 + sum))))
            else
              (do
                (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
                  (Sail.BitVec.castWidth sum))) ) : SailM (BitVec datasize) )
          (pure ((op1, op2, result, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × (BitVec (2 * esize))) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4752)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4753) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4754) ()) ) : SailM Int )
  let sum ← (( do (undefined_int_at (← occLabel 4755) ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, sum) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let sum : Int :=
            if (sub_op : Bool)
            then (element1 -i element2)
            else (element1 +i element2)
          let w__4 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange sum ((2 *i esize) -i 1) 0))) ) : SailM
            (BitVec (2 * datasize)) )
          let result := (w__4 : (BitVec (2 * datasize)))
          (pure ((element1, element2, result, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec (2 * datasize)) × Int) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_add_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand 0 esize)) ) : SailM
    (BitVec esize) )
  let sum ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
  let sum ← (( do
    let loop_e_lower : Nat := 1
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := sum
      for e in [loop_e_lower:loop_e_upper:1]i do
        let sum := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let sum : Int := ((sum +i w__2) : Int)
          (pure (sum))
      (pure loop_vars)) ) : SailM Int )
  let sum : Int := sum
  (V_set d (Sail.Int.toNatChecked ((2 *i esize)))
    (Sail.BitVec.castWidth (integer_subrange sum ((2 *i esize) -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4756)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4757) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4758) ()) ) : SailM Int )
  let sum ← (( do (undefined_int_at (← occLabel 4759) ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, sum) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let sum : Int :=
            if (sub_op : Bool)
            then (element1 -i element2)
            else (element1 +i element2)
          let w__4 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange sum ((2 *i esize) -i 1) 0))) ) : SailM
            (BitVec (2 * datasize)) )
          let result := (w__4 : (BitVec (2 * datasize)))
          (pure ((element1, element2, result, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec (2 * datasize)) × Int) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_signed : Bool, m :
  Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_signed : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res : Int := 0
          let element1 ← (( do (undefined_int_at (← occLabel 4763) ()) ) : SailM Int )
          let element2 ← (( do (undefined_int_at (← occLabel 4764) ()) ) : SailM Int )
          let (element1, element2, res) ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := (element1, element2, res)
              for i in [loop_i_lower:loop_i_upper:1]i do
                let (element1, element2, res) := loop_vars_1
                loop_vars_1 ← do
                  let (element1, element2) ← (( do
                    if (is_signed : Bool)
                    then
                      (do
                        let w__0 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element1 : Int := ((BitVec.toInt w__0) : Int)
                        let w__1 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element2 : Int := ((BitVec.toInt w__1) : Int)
                        (pure ((element1, element2))))
                    else
                      (do
                        let w__2 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element1 : Int := ((BitVec.toNat w__2) : Int)
                        let w__3 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element2 : Int := ((BitVec.toNat w__3) : Int)
                        (pure ((element1, element2)))) ) : SailM (Int × Int) )
                  let res : Int := (res +i (element1 *i element2))
                  (pure ((element1, element2, res)))
              (pure loop_vars_1)) ) : SailM (Int × Int × Int) )
          let res : Int := res
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt w__4 res)))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, index : Nat, k_is_signed
  : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_dotp (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (is_signed : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res : Int := 0
          let element1 ← (( do (undefined_int_at (← occLabel 4765) ()) ) : SailM Int )
          let element2 ← (( do (undefined_int_at (← occLabel 4766) ()) ) : SailM Int )
          let (element1, element2, res) ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := (element1, element2, res)
              for i in [loop_i_lower:loop_i_upper:1]i do
                let (element1, element2, res) := loop_vars_1
                loop_vars_1 ← do
                  let (element1, element2) ← (( do
                    if (is_signed : Bool)
                    then
                      (do
                        let w__0 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element1 : Int := ((BitVec.toInt w__0) : Int)
                        let w__1 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i index) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element2 : Int := ((BitVec.toInt w__1) : Int)
                        (pure ((element1, element2))))
                    else
                      (do
                        let w__2 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element1 : Int := ((BitVec.toNat w__2) : Int)
                        let w__3 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i index) +i i)
                            (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                          (BitVec (esize / 4)) )
                        let element2 : Int := ((BitVec.toNat w__3) : Int)
                        (pure ((element1, element2)))) ) : SailM (Int × Int) )
                  let res : Int := (res +i (element1 *i element2))
                  (pure ((element1, element2, res)))
              (pure loop_vars_1)) ) : SailM (Int × Int × Int) )
          let res : Int := res
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt w__4 res)))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n))))


def decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n))))


def decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let part1 : Bool := (P == 0#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part1))


def decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let part1 : Bool := (P == 0#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part1))


def decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n))))


def decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sha512_sha512h (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sha512_sha512h2 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sha512_sha512su0 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n))))


def decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
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
      (execute_aarch64_instrs_vector_crypto_sha512_sha512su1 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4795)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4796) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4797) ()) ) : SailM Int )
  let sum ← (( do (undefined_int_at (← occLabel 4798) ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, sum) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let sum : Int := (Int.shiftr (element1 +i element2) 1)
          let w__4 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange sum (esize -i 1) 0)))
            ) : SailM (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, result, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Int) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Int, elements : Int, esize : Int, n : Nat, shift : Int, 0
  ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_sisd (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:44321.56-44321.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (datasize))))
    ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4799)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          ArmFull.assert (esize ≥b 0) "sail-inputs/15-instrs64.sail:44325.38-44325.39"
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))))) "sail-inputs/15-instrs64.sail:44326.179-44326.180"
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          (Elem_set result e (Sail.Int.toNatChecked (esize))
            (Sail.BitVec.castWidth (w__0 <<< shift)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  (V_set d (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth result))


end ArmFull.Functions
