import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0152
import ArmFull.Fn.M0215
import ArmFull.Fn.M0852
import ArmFull.Fn.M0854

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

def decode_yield_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp (← occLabel 4026) ()) ) : SailM SystemHintOp )
  let op ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0000000 => (pure (SystemHintOp_NOP))
    | 0b0000001 => (pure (SystemHintOp_YIELD))
    | 0b0000010 => (pure (SystemHintOp_WFE))
    | 0b0000011 => (pure (SystemHintOp_WFI))
    | 0b0000100 => (pure (SystemHintOp_SEV))
    | 0b0000101 => (pure (SystemHintOp_SEVL))
    | 0b0000110 =>
      (do
        let w__0 ← (( do (HaveDGHExt ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            (EndOfInstruction ()))
        else (pure (()))
        (pure (SystemHintOp_DGH)))
    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (do
            match op2 with
            | 0b000 => sailThrow ((Error_See "PACIA1716"))
            | 0b010 => sailThrow ((Error_See "PACIB1716"))
            | 0b100 => sailThrow ((Error_See "AUTIA1716"))
            | 0b110 => sailThrow ((Error_See "AUTIB1716"))
            | _ =>
              (do
                (EndOfInstruction ()))
            (pure (op)))
        else
          (do
            match b__0 with
            | 0b0010000 =>
              (do
                let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_ESB)))
            | 0b0010001 =>
              (do
                let w__2 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_PSB)))
            | 0b0010010 =>
              (do
                let w__3 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
                if ((! w__3) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_TSB)))
            | 0b0010011 =>
              (do
                let w__4 ← (( do (IsFeatureImplemented FEAT_GCS) ) : SailM Bool )
                if ((! w__4) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_GCSB)))
            | 0b0010100 => (pure (SystemHintOp_CSDB))
            | 0b0010110 =>
              (do
                let w__5 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
                if ((! w__5) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_CLRBHB)))
            | b__0 =>
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x3#4 : (BitVec 4))) : Bool)
                then
                  (do
                    match op2 with
                    | 0b000 => sailThrow ((Error_See "PACIAZ"))
                    | 0b001 => sailThrow ((Error_See "PACIASP"))
                    | 0b010 => sailThrow ((Error_See "PACIBZ"))
                    | 0b011 => sailThrow ((Error_See "PACIBSP"))
                    | 0b100 => sailThrow ((Error_See "AUTIAZ"))
                    | 0b101 => sailThrow ((Error_See "AUTIASP"))
                    | 0b110 => sailThrow ((Error_See "AUTIBZ"))
                    | _ => sailThrow ((Error_See "AUTIBSP"))
                    (pure (op)))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                    then
                      (do
                        let op : SystemHintOp := SystemHintOp_BTI
                        let w__6 ← (( do (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1)) )
                          : SailM Bool )
                        (SetBTypeCompatible w__6)
                        (pure (op)))
                    else
                      (do
                        match b__0 with
                        | 0b0101000 =>
                          (do
                            let w__7 ← (( do (IsFeatureImplemented FEAT_CHK) ) : SailM Bool )
                            if ((! w__7) : Bool)
                            then
                              (do
                                (EndOfInstruction ()))
                            else (pure (()))
                            (pure (SystemHintOp_CHKFEAT)))
                        | _ =>
                          (do
                            (EndOfInstruction ())
                            (pure (op)))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_clsz (countop : CountOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4029)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let count ← (( do (undefined_int_at (← occLabel 4030) ()) ) : SailM Int )
  let (count, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, result) := loop_vars
        loop_vars ← do
          let count ← (( do
            if ((BEq.beq countop CountOp_CLS) : Bool)
            then
              (do
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                  SailM (BitVec esize) )
                let count : Int := ((CountLeadingSignBits w__0) : Int)
                (pure (count)))
            else
              (do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                  SailM (BitVec esize) )
                let count : Int := ((CountLeadingZeroBits w__1) : Int)
                (pure (count))) ) : SailM Int )
          let w__2 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange count (esize -i 1) 0)))
            ) : SailM (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((count, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4032)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4033) ()) ) : SailM Int )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4034) ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, test_passed) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element : Int := ((BitVec.toInt w__0) : Int)
          let test_passed : Bool :=
            match comparison with
            | .CompareOp_GT => (element >b 0)
            | .CompareOp_GE => (element ≥b 0)
            | .CompareOp_EQ => (element == 0)
            | .CompareOp_LE => (element ≤b 0)
            | .CompareOp_LT => (element <b 0)
          let w__1 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize))))) ) : SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((element, result, test_passed)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_and_test : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m :
  Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (and_test : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4043)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4044)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4045)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4046) ()) ) : SailM Bool )
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, test_passed) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let test_passed : Bool :=
            if (and_test : Bool)
            then (! (IsZero (element1 &&& element2)))
            else (element1 == element2)
          let w__2 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize))))) ) : SailM (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element1, element2, result, test_passed)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_cmp_eq : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (cmp_eq : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4047)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4048) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4049) ()) ) : SailM Int )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4050) ()) ) : SailM Bool )
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, test_passed) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let test_passed : Bool :=
            if (cmp_eq : Bool)
            then (element1 ≥b element2)
            else (element1 >b element2)
          let w__4 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize))))) ) : SailM (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, result, test_passed)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4051)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4052) ()) ) : SailM Int )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4053) ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, test_passed) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element : Int := ((BitVec.toInt w__0) : Int)
          let test_passed : Bool :=
            match comparison with
            | .CompareOp_GT => (element >b 0)
            | .CompareOp_GE => (element ≥b 0)
            | .CompareOp_EQ => (element == 0)
            | .CompareOp_LE => (element ≤b 0)
            | .CompareOp_LT => (element <b 0)
          let w__1 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize))))) ) : SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((element, result, test_passed)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 8 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cnt (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4054)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let count ← (( do (undefined_int_at (← occLabel 4055) ()) ) : SailM Int )
  let (count, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := (count, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let count : Int := ((BitCount w__0) : Int)
          let w__1 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange count (esize -i 1) 0)))
            ) : SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((count, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64, 128, 256] ∧
  List.elem datasize [8, 16, 32, 64, 128, 256] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4102)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand index esize)) ) : SailM
    (BitVec esize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do (Elem_set result e esize (Sail.BitVec.castWidth element))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-arm/instrs64.sail:10473.56-10473.57"
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64, 128, 256] ∧
  List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_dup (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:10541.48-10541.49"
  let element ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n esize)) ) : SailM (BitVec esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4103)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do (Elem_set result e esize (Sail.BitVec.castWidth element))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  (execute_aarch64_instrs_vector_crypto_sha3_eor3 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, position : Int, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_extract (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (position : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let hi ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM (BitVec datasize) )
  let lo ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM (BitVec datasize) )
  let concat : (BitVec (datasize * 2)) := (Sail.BitVec.castWidth (hi +++ lo))
  ArmFull.assert ((0 ≤b position) && (((position +i datasize) -i 1) <b (datasize *i 2))) "sail-arm/instrs64.sail:10696.83-10696.84"
  (V_set d datasize
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
      (Sail.Int.toNatChecked (((position +i datasize) -i 1))) (Sail.Int.toNatChecked (position)))))


def decode_fcsel_float_aarch64_instrs_float_move_fp_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize : Int := datasize
  let condition : (BitVec 4) := cond
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
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize : Int := datasize
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (VFPExpandImm imm8 (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:22661.48-22661.49"
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


end ArmFull.Functions
