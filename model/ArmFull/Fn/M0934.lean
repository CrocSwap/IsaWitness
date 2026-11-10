import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0145
import ArmFull.Fn.M0215
import ArmFull.Fn.M0852
import ArmFull.Fn.M0854
import ArmFull.Fn.M0855

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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)))


def decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)))


def decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let part1 : Bool := (P == 0#1)
  (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part1)


def decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let part1 : Bool := (P == 0#1)
  (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part1)


def decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)))


def decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512h (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512h2 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512su0 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)))


def decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA512Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512su1 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


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
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:44321.56-44321.57"
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
          ArmFull.assert (esize ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:44325.38-44325.39"
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:44326.179-44326.180"
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          (Elem_set result e (Sail.Int.toNatChecked (esize))
            (Sail.BitVec.castWidth (w__0 <<< shift)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  (V_set d (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth result))


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
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:44507.56-44507.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (datasize))))
    ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4806)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  ArmFull.assert (esize ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:44511.34-44511.35"
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
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || ((! (esize ≥b 0)) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:44515.198-44515.199"
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let i : Int := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let i : Int := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let i : Int := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let i : Int := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM4Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  (execute_aarch64_instrs_vector_crypto_sm4_sm4enc (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)))


def decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSM4Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sm4_sm4enckey (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


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


end ArmFull.Functions
