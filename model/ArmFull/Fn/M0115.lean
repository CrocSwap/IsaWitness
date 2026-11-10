import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0024
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046

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

def SHAhashSIGMA0 (x : (BitVec 32)) : (BitVec 32) :=
  (((ROR x 2) ^^^ (ROR x 13)) ^^^ (ROR x 22))


def SHAhashSIGMA1 (x : (BitVec 32)) : (BitVec 32) :=
  (((ROR x 6) ^^^ (ROR x 11)) ^^^ (ROR x 25))


def _set_CONTEXTIDR_EL1_Type_PROCID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CONTEXTIDR_EL1_Type_PROCID r v)


def _set_CONTEXTIDR_EL2_Type_PROCID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CONTEXTIDR_EL2_Type_PROCID r v)


def _set_TTBCR_Type_EAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR_Type_EAE r v)


def _set_TTBCR_Type_PD0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR_Type_PD0 r v)


def _set_TTBCR_Type_PD1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR_Type_PD1 r v)


def _set_TTBCR_Type_T2E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR_Type_T2E r v)


def _set_CONTEXTIDR_Type_ASID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CONTEXTIDR_Type_ASID r v)


def _set_TTBR0_EL1_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL1_Type_ASID r v)


def _set_TTBR0_EL2_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL2_Type_ASID r v)


def _set_TTBR0_Type_ASID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_ASID r v)


def _set_TTBR1_EL1_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL1_Type_ASID r v)


def _set_TTBR1_EL2_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL2_Type_ASID r v)


def _set_TTBR1_Type_ASID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_ASID r v)


def _set_TTBR0_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_BADDR r v)


def _set_GPTBR_EL3_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPTBR_EL3_Type_BADDR r v)


def _set_HTTBR_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HTTBR_Type_BADDR r v)


def _set_TTBR1_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_BADDR r v)


def _set_VNCR_EL2_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 45)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VNCR_EL2_Type_BADDR r v)


def _set_VTTBR_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTTBR_Type_BADDR r v)


def _set_TTBR0_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_CnP r v)


def _set_HTTBR_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HTTBR_Type_CnP r v)


def _set_ID_AA64MMFR2_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_CnP r v)


def _set_ID_MMFR4_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_CnP r v)


def _set_ID_MMFR4_Type_CnP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_CnP r v)


def _set_TTBR0_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL1_Type_CnP r v)


def _set_TTBR0_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL2_Type_CnP r v)


def _set_TTBR0_EL3_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_EL3_Type_CnP r v)


def _set_TTBR1_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL1_Type_CnP r v)


def _set_TTBR1_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL2_Type_CnP r v)


def _set_TTBR1_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_CnP r v)


def _set_VSTTBR_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTTBR_EL2_Type_CnP r v)


def _set_VTTBR_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_VTTBR_EL2_Type_CnP r v)


def _set_VTTBR_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTTBR_Type_CnP r v)


def _set_TTBR0_Type_IRGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_IRGN r v)


def _set_GPCCR_EL3_Type_IRGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_IRGN r v)


def _set_TTBR1_Type_IRGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_IRGN r v)


def _set_TTBR0_Type_NOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_NOS r v)


def _set_PAR_Type_NOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_NOS r v)


def _set_TTBR1_Type_NOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_NOS r v)


def _set_TTBR0_Type_RGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_RGN r v)


def _set_TTBR1_Type_RGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_RGN r v)


def _set_TTBR0_Type_TTB0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_TTB0 r v)


def _set_TTBR0_EL1_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL1_Type_SKL r v)


def _set_TTBR0_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR0_EL2_Type_SKL r v)


def _set_TTBR0_EL3_Type_SKL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_EL3_Type_SKL r v)


def _set_TTBR1_EL1_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL1_Type_SKL r v)


def _set_TTBR1_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_TTBR1_EL2_Type_SKL r v)


def _set_VSTTBR_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTTBR_EL2_Type_SKL r v)


def _set_VTTBR_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_VTTBR_EL2_Type_SKL r v)


def _set_TTBR1_Type_TTB1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_TTB1 r v)


/-- Type quantifiers: a_in : Int, k_increasedprecision_name : Bool -/
def RecipEstimate (a_in : Int) (increasedprecision_name : Bool) : SailM Int := do
  let a : Int := a_in
  let r ← (( do (undefined_int_at (← occLabel 811) ()) ) : SailM Int )
  let r ← (( do
    if ((! increasedprecision_name) : Bool)
    then
      (do
        ArmFull.assert ((256 ≤b a) && (a <b 512)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13058.33-13058.34"
        let a : Int := ((a *i 2) +i 1)
        let b : Int := (fdiv_int (2 ^i 19) a)
        let r : Int := (fdiv_int (b +i 1) 2)
        ArmFull.assert ((256 ≤b r) && (r <b 512)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13062.33-13062.34"
        (pure (r)))
    else
      (do
        ArmFull.assert ((2048 ≤b a) && (a <b 4096)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13064.35-13064.36"
        let a : Int := ((a *i 2) +i 1)
        let real_val : real := (div_real (to_real (2 ^i 25)) (to_real a))
        let r : Int := (round_down real_val)
        let error : real := (sub_real real_val (to_real r))
        let round_up : Bool := (gt_real error (1/2))
        let r : Int :=
          if (round_up : Bool)
          then (r +i 1)
          else r
        ArmFull.assert ((4096 ≤b r) && (r <b 8192)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13073.35-13073.36"
        (pure (r))) ) : SailM Int )
  let r : Int := r
  (pure (r))


/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def SignedSatQ (i : Int) (N : Nat) : SailM ((BitVec N) × Bool) := do
  let result ← (( do (undefined_int_at (← occLabel 821) ()) ) : SailM Int )
  let saturated ← (( do (undefined_bool_at (← occLabel 822) ()) ) : SailM Bool )
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i (N -i 1)) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i (N -i 1)) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b (Neg.neg (2 ^i (N -i 1)))) : Bool)
        then
          (let result : Int := (Neg.neg (2 ^i (N -i 1)))
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  let result : Int := result
  (pure (((Sail.BitVec.castWidth (integer_subrange result (N -i 1) 0)), saturated)))


/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def UnsignedSatQ (i : Int) (N : Nat) : SailM ((BitVec N) × Bool) := do
  let result ← (( do (undefined_int_at (← occLabel 823) ()) ) : SailM Int )
  let saturated ← (( do (undefined_bool_at (← occLabel 824) ()) ) : SailM Bool )
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i N) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i N) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b 0) : Bool)
        then
          (let result : Int := 0
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  let result : Int := result
  (pure (((Sail.BitVec.castWidth (integer_subrange result (N -i 1) 0)), saturated)))


/-- Type quantifiers: k_M : Nat, k_N : Nat, k_M ≥ 0 ∧ k_N ≥ 0 -/
def PolynomialMult (op1 : (BitVec k_M)) (op2 : (BitVec k_N)) : (BitVec (k_M + k_N)) := Id.run do
  let result : (BitVec (k_M + k_N)) :=
    (Sail.BitVec.castWidth (Zeros
      (n := (Sail.Int.toNatChecked (((Sail.BitVec.length op1) +i (Sail.BitVec.length op2)))))))
  let extended_op2 : (BitVec (k_M + k_N)) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend op2
      (Sail.Int.toNatChecked (((Sail.BitVec.length op1) +i (Sail.BitVec.length op2))))))
  let loop_i_lower : Nat := 0
  let loop_i_upper : Int := ((Sail.BitVec.length op1) -i 1)
  ((Sail.BitVec.castWidth ) <$> (do
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op1 (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
        then (result ^^^ (extended_op2 <<< i))
        else result
    (pure loop_vars)))


/-- Type quantifiers: k_N : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_N = 128 -/
def MatMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length op2) == 128) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13317.20-13317.21"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 837)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let sum ← (( do (undefined_bitvector_at (← occLabel 838) 32) ) : SailM (BitVec 32) )
  let prod ← (( do (undefined_int_at (← occLabel 839) ()) ) : SailM Int )
  let (prod, result, sum) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 1
    (do
      let mut loop_vars := (prod, result, sum)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (prod, result, sum) := loop_vars
        loop_vars ← do
          let loop_j_lower : Nat := 0
          let loop_j_upper : Nat := 1
          (do
            let mut loop_vars_1 := (prod, result, sum)
            for j in [loop_j_lower:loop_j_upper:1]i do
              let (prod, result, sum) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (Elem_read addend ((2 *i i) +i j) 32) ) : SailM (BitVec 32) )
                let sum := (w__0 : (BitVec 32))
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 7
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__1 ← (( do (Elem_read op1 ((8 *i i) +i k) 8) ) : SailM (BitVec 8) )
                        let w__2 ← (( do (asl_Int w__1 op1_unsigned) ) : SailM Int )
                        let w__3 ← (( do (Elem_read op2 ((8 *i j) +i k) 8) ) : SailM (BitVec 8) )
                        let w__4 ← (( do (asl_Int w__3 op2_unsigned) ) : SailM Int )
                        let prod : Int := ((w__2 *i w__4) : Int)
                        let sum : (BitVec 32) := (BitVec.addInt sum prod)
                        (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec 32)) )
                let w__5 ← (( do (Elem_set result ((2 *i i) +i j) 32 sum) ) : SailM (BitVec k_N) )
                let result := (w__5 : (BitVec k_N))
                (pure ((prod, result, sum)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec k_N) × (BitVec 32)) )
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_N : Nat, k_N > 0 -/
def AddWithCarry (x : (BitVec k_N)) (y : (BitVec k_N)) (carry_in : (BitVec 1)) : ((BitVec k_N) × (BitVec 4)) :=
  let unsigned_sum : Int := (((BitVec.toNat x) +i (BitVec.toNat y)) +i (BitVec.toNat carry_in))
  let signed_sum : Int := (((BitVec.toInt x) +i (BitVec.toInt y)) +i (BitVec.toNat carry_in))
  let result : (BitVec k_N) :=
    (Sail.BitVec.castWidth (integer_subrange unsigned_sum ((Sail.BitVec.length y) -i 1) 0))
  let n : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
        (Sail.Int.toNatChecked (((Sail.BitVec.length y) -i 1))))]))
  let z : (BitVec 1) :=
    if ((IsZero result) : Bool)
    then 1#1
    else 0#1
  let c : (BitVec 1) :=
    if (((BitVec.toNat result) == unsigned_sum) : Bool)
    then 0#1
    else 1#1
  let v : (BitVec 1) :=
    if (((BitVec.toInt result) == signed_sum) : Bool)
    then 0#1
    else 1#1
  (result, (((n +++ z) +++ c) +++ v))


def IsExternalSyncAbort__1 (fault : FaultRecord) : SailM Bool := do
  (pure ((← do
        (IsExternalSyncAbort fault.statuscode)) || ((BEq.beq fault.gpcf.gpf GPCF_EABT) : Bool)))


/-- Type quantifiers: k_iswrite : Bool, size : Int -/
def IsExternalAbortTakenSynchronously (memstatus : PhysMemRetStatus) (iswrite : Bool) (desc : AddressDescriptor) (size : Int) (accdesc : AccessDescriptor) : SailM Bool := do
  (__UNKNOWN_boolean ())


def AArch32_EncodeAsyncErrorSyndrome (errorstate : ErrorState) : SailM (BitVec 2) := do
  match errorstate with
  | .ErrorState_UC => (pure (0b00#2))
  | .ErrorState_UEU => (pure (0b01#2))
  | .ErrorState_UEO => (pure (0b10#2))
  | .ErrorState_UER => (pure (0b11#2))
  | _ =>
    (do
      (Unreachable ())
      (undefined_bitvector_at (← occLabel 840) 2))


def ActionRequired (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ErrorIsContained (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ErrorIsSynchronized (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ReportErrorAsUC (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ReportErrorAsUER (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ReportErrorAsUEU (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def StateIsRecoverable (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def IsAsyncAbort__1 (fault : FaultRecord) : SailM Bool := do
  (IsAsyncAbort fault.statuscode)


def IsExternalAbort__1 (fault : FaultRecord) : SailM Bool := do
  (pure ((← do
        (IsExternalAbort fault.statuscode)) || ((BEq.beq fault.gpcf.gpf GPCF_EABT) : Bool)))


def LSInstructionSyndrome (_ : Unit) : (BitVec 11) :=
  (Zeros (n := 11))


def AArch32_ExceptionClass (exceptype : Exception) : SailM (Int × (BitVec 1)) := do
  let il_is_valid : Bool := true
  let ec ← (( do (undefined_int_at (← occLabel 842) ()) ) : SailM Int )
  let (ec, il_is_valid) ← (( do
    match exceptype with
    | .Exception_Uncategorized =>
      (let ec : Int := (BitVec.toNat 0x00#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_WFxTrap =>
      (let ec : Int := (BitVec.toNat 0x01#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP15RTTrap =>
      (let ec : Int := (BitVec.toNat 0x03#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP15RRTTrap =>
      (let ec : Int := (BitVec.toNat 0x04#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP14RTTrap =>
      (let ec : Int := (BitVec.toNat 0x05#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP14DTTrap =>
      (let ec : Int := (BitVec.toNat 0x06#8)
      (pure ((ec, il_is_valid))))
    | .Exception_AdvSIMDFPAccessTrap =>
      (let ec : Int := (BitVec.toNat 0x07#8)
      (pure ((ec, il_is_valid))))
    | .Exception_FPIDTrap =>
      (let ec : Int := (BitVec.toNat 0x08#8)
      (pure ((ec, il_is_valid))))
    | .Exception_PACTrap =>
      (let ec : Int := (BitVec.toNat 0x09#8)
      (pure ((ec, il_is_valid))))
    | .Exception_TSTARTAccessTrap =>
      (let ec : Int := (BitVec.toNat 0x1B#8)
      (pure ((ec, il_is_valid))))
    | .Exception_GPC =>
      (let ec : Int := (BitVec.toNat 0x1E#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP14RRTTrap =>
      (let ec : Int := (BitVec.toNat 0x0C#8)
      (pure ((ec, il_is_valid))))
    | .Exception_BranchTarget =>
      (let ec : Int := (BitVec.toNat 0x0D#8)
      (pure ((ec, il_is_valid))))
    | .Exception_IllegalState =>
      (let ec : Int := (BitVec.toNat 0x0E#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_SupervisorCall =>
      (let ec : Int := (BitVec.toNat 0x11#8)
      (pure ((ec, il_is_valid))))
    | .Exception_HypervisorCall =>
      (let ec : Int := (BitVec.toNat 0x12#8)
      (pure ((ec, il_is_valid))))
    | .Exception_MonitorCall =>
      (let ec : Int := (BitVec.toNat 0x13#8)
      (pure ((ec, il_is_valid))))
    | .Exception_InstructionAbort =>
      (let ec : Int := (BitVec.toNat 0x20#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_PCAlignment =>
      (let ec : Int := (BitVec.toNat 0x22#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_DataAbort =>
      (let ec : Int := (BitVec.toNat 0x24#8)
      (pure ((ec, il_is_valid))))
    | .Exception_NV2DataAbort =>
      (let ec : Int := (BitVec.toNat 0x25#8)
      (pure ((ec, il_is_valid))))
    | .Exception_FPTrappedException =>
      (let ec : Int := (BitVec.toNat 0x28#8)
      (pure ((ec, il_is_valid))))
    | _ =>
      (do
        (Unreachable ())
        (pure ((ec, il_is_valid)))) ) : SailM (Int × Bool) )
  let w__1 ← (( do
    if ((((ec == (BitVec.toNat 0x20#8)) || ((ec == (BitVec.toNat 0x24#8)) : Bool)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__0.EL == EL2) : Bool))))
    else (pure false) ) : SailM Bool )
  let ec : Int :=
    if (w__1 : Bool)
    then (ec +i 1)
    else ec
  let ec : Int := ec
  let il ← (( do (undefined_bitvector_at (← occLabel 843) 1) ) : SailM (BitVec 1) )
  let il ← (( do
    if (il_is_valid : Bool)
    then
      (do
        let w__2 ← (( do (ThisInstrLength ()) ) : SailM Int )
        let w__3 : (BitVec 1) :=
          if ((w__2 == 32) : Bool)
          then 1#1
          else 0#1
        (pure ((w__3 : (BitVec 1)))))
    else (pure (1#1)) ) : SailM (BitVec 1) )
  (pure ((ec, il)))


def _set_MVBAR_Type_Reserved (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVBAR_Type_Reserved r v)


/-- Type quantifiers: level : Int -/
def EncodeSDFSC (statuscode : Fault) (level : Int) : SailM (BitVec 5) := do
  let result ← (( do (undefined_bitvector_at (← occLabel 849) 5) ) : SailM (BitVec 5) )
  match statuscode with
  | .Fault_AccessFlag =>
    (do
      ArmFull.assert ((level == 1) || (level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14174.40-14174.41"
      let result : (BitVec 5) :=
        if ((level == 1) : Bool)
        then 0b00011#5
        else 0b00110#5
      (pure (result)))
  | .Fault_Alignment => (pure (0b00001#5))
  | .Fault_Permission =>
    (do
      ArmFull.assert ((level == 1) || (level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14181.40-14181.41"
      let result : (BitVec 5) :=
        if ((level == 1) : Bool)
        then 0b01101#5
        else 0b01111#5
      (pure (result)))
  | .Fault_Domain =>
    (do
      ArmFull.assert ((level == 1) || (level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14185.40-14185.41"
      let result : (BitVec 5) :=
        if ((level == 1) : Bool)
        then 0b01001#5
        else 0b01011#5
      (pure (result)))
  | .Fault_Translation =>
    (do
      ArmFull.assert ((level == 1) || (level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14189.40-14189.41"
      let result : (BitVec 5) :=
        if ((level == 1) : Bool)
        then 0b00101#5
        else 0b00111#5
      (pure (result)))
  | .Fault_SyncExternal => (pure (0b01000#5))
  | .Fault_SyncExternalOnWalk =>
    (do
      ArmFull.assert ((level == 1) || (level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14196.40-14196.41"
      let result : (BitVec 5) :=
        if ((level == 1) : Bool)
        then 0b01100#5
        else 0b01110#5
      (pure (result)))
  | .Fault_SyncParity => (pure (0b11001#5))
  | .Fault_SyncParityOnWalk =>
    (do
      ArmFull.assert ((level == 1) || (level == 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14203.40-14203.41"
      let result : (BitVec 5) :=
        if ((level == 1) : Bool)
        then 0b11100#5
        else 0b11110#5
      (pure (result)))
  | .Fault_AsyncParity => (pure (0b11000#5))
  | .Fault_AsyncExternal => (pure (0b10110#5))
  | .Fault_Debug => (pure (0b00010#5))
  | .Fault_TLBConflict => (pure (0b10000#5))
  | .Fault_Lockdown => (pure (0b10100#5))
  | .Fault_Exclusive => (pure (0b10101#5))
  | .Fault_ICacheMaint => (pure (0b00100#5))
  | _ =>
    (do
      (Unreachable ())
      (pure (result)))


end ArmFull.Functions
