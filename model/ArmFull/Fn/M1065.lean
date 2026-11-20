module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0255
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0956
public import ArmFull.Fn.M0965
public import ArmFull.Fn.M0966 set_option backward.proofsInPublic true @[expose] public section

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

def decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((size == 3) && (Q == 0#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 size)
          let datasize : Int :=
            if ((Q == 1#1) : Bool)
            then 128
            else 64
          let elements : Int := (fdiv_int datasize esize)
          ArmFull.assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "sail-inputs/15-instrs64.sail:10565.58-10565.59"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_transfer_integer_dup (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)))))


def decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((Q == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm4 3)])) == 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let position : Int := (Int.shiftl (BitVec.toNat imm4) 3)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_transfer_vector_extract (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        position))


def decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let rd : Int := (BitVec.toNat Rd)
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let imm8 : (BitVec 8) := (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)
      let imm16 : (BitVec 16) :=
        (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 7)])) +++ (Complement.complement
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])))) +++ (BitVec.replicateBits
                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])) 2)) +++ (Sail.BitVec.extractLsb
              imm8 5 0)) +++ (Zeros (n := 6)))
      let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
        (Sail.BitVec.castWidth (BitVec.replicateBits imm16
          (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 16)))))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_fp16_movi (Sail.Int.toNatChecked (datasize))
        (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (rd))))


def decode_fmov_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp (← occLabel 4285) ()) ) : SailM ImmediateOp )
  let b__0 := (cmode +++ op)
  let operation ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure (ImmediateOp_MOVI))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure (ImmediateOp_MVNI))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure (ImmediateOp_ORR))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure (ImmediateOp_BIC))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure (ImmediateOp_MOVI))
                    else
                      (do
                        if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure (ImmediateOp_MVNI))
                        else
                          (do
                            if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure (ImmediateOp_ORR))
                            else
                              (do
                                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4
                                         3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure (ImmediateOp_BIC))
                                else
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure (ImmediateOp_MOVI))
                                    else
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure (ImmediateOp_MVNI))
                                        else
                                          (do
                                            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure (ImmediateOp_MOVI))
                                            else
                                              (do
                                                match b__0 with
                                                | 0b11110 => (pure (ImmediateOp_MOVI))
                                                | _ =>
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then
                                                      (do
                                                        (__ArmCertEndOfDecode ())
                                                        sailThrow ((Error_Undefined ())))
                                                    else (pure (ImmediateOp_MOVI)))))))))))))) ) :
    SailM ImmediateOp )
  let operation := operation
  let imm64 ← (( do
    (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM
    (BitVec 64) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm64
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 64)))))
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_fp16_movi (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (rd)))


def decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      ArmFull.assert (0 ≤b (size +i 1)) "sail-inputs/15-instrs64.sail:22555.37-22555.38"
      let dst_index : Int :=
        (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
      ArmFull.assert (0 ≤b size) "sail-inputs/15-instrs64.sail:22557.33-22557.34"
      let src_index : Int :=
        (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 (Sail.Int.toNatChecked (size))))
      let idxdsize : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm4 3)])) == 1#1) : Bool)
        then 128
        else 64
      let esize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (size)))
      match esize with
      | 8 =>
        (do
          match idxdsize with
          | 64 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 8 64 (Sail.Int.toNatChecked (n)) src_index))
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 8 128 (Sail.Int.toNatChecked (n)) src_index))
          | _ =>
            (do
              ArmFull.assert false "sail-inputs/15-instrs64.sail:22571.28-22571.29"
              throw Error.Exit))
      | 16 =>
        (do
          match idxdsize with
          | 64 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 16 64 (Sail.Int.toNatChecked (n)) src_index))
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 16 128 (Sail.Int.toNatChecked (n)) src_index))
          | _ =>
            (do
              ArmFull.assert false "sail-inputs/15-instrs64.sail:22584.28-22584.29"
              throw Error.Exit))
      | 32 =>
        (do
          match idxdsize with
          | 64 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 32 64 (Sail.Int.toNatChecked (n)) src_index))
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 32 128 (Sail.Int.toNatChecked (n)) src_index))
          | _ =>
            (do
              ArmFull.assert false "sail-inputs/15-instrs64.sail:22597.28-22597.29"
              throw Error.Exit))
      | 64 =>
        (do
          match idxdsize with
          | 64 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 64 64 (Sail.Int.toNatChecked (n)) src_index))
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
                dst_index 64 128 (Sail.Int.toNatChecked (n)) src_index))
          | _ =>
            (do
              ArmFull.assert false "sail-inputs/15-instrs64.sail:22610.28-22610.29"
              throw Error.Exit))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/15-instrs64.sail:22641.22-22641.23"
          throw Error.Exit))


def decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      ArmFull.assert (0 ≤b (size +i 1)) "sail-inputs/15-instrs64.sail:22677.37-22677.38"
      let index : Int :=
        (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
      let esize : Int := (_shl_int_general 8 size)
      let datasize : Nat := 128
      ArmFull.assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "sail-inputs/15-instrs64.sail:22681.58-22681.59"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_transfer_integer_insert (Sail.Int.toNatChecked (d)) datasize
        (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (n))))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcgettag (n : Nat) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4439) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (address + offset)
  let address : (BitVec 64) := (Align_bits address TAG_GRANULE)
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_LOAD) ) : SailM AccessDescriptor )
  let tag ← (( do (AArch64_MemTag_read address accdesc) ) : SailM (BitVec 4) )
  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let w__3 ← (( do (AArch64_AddressWithAllocationTag w__2 tag) ) : SailM (BitVec 64) )
  (X_set t 64 w__3)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcgettagarray (n : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let data : (BitVec 64) := (Zeros (n := 64))
  let address ← (( do (undefined_bitvector_at (← occLabel 4440) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__3 ← (( do readReg GMID_EL1 ) : SailM (BitVec 64) )
  let size : Nat :=
    (Sail.Int.toNatChecked ((4 *i (2 ^i (BitVec.toNat (_get_GMID_EL1_Type_BS w__3))))))
  let address : (BitVec 64) := (Align_bits address size)
  let count : Int := (Int.shiftr size LOG2_TAG_GRANULE)
  let index : Int :=
    (BitVec.toNat
      (Sail.BitVec.extractLsb address (Sail.Int.toNatChecked ((LOG2_TAG_GRANULE +i 3)))
        LOG2_TAG_GRANULE))
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_LOAD) ) : SailM AccessDescriptor )
  let (address, data, index) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (count -i 1)
    (do
      let mut loop_vars := (address, data, index)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (address, data, index) := loop_vars
        loop_vars ← do
          let tag ← (( do (AArch64_MemTag_read address accdesc) ) : SailM (BitVec 4) )
          let index : Int := index
          ArmFull.assert ((0 ≤b (index *i 4)) && (((index *i 4) +i 3) <b 64)) "sail-inputs/15-instrs64.sail:30614.72-30614.73"
          let data : (BitVec 64) :=
            (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked (((index *i 4) +i 3)))
              (Sail.Int.toNatChecked ((index *i 4))) (Sail.BitVec.castWidth tag))
          let address : (BitVec 64) := (BitVec.addInt address TAG_GRANULE)
          let index : Int := (index +i 1)
          (pure ((address, data, index)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × Int) )
  (X_set t 64 data)


def decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        sub_op))


def decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        sub_op))


def decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4654) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4655) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op)


def decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4656) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4657) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op)


def decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((U == 1#1) && (size != 0b00#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b11#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let datasize : Int :=
            if ((Q == 1#1) : Bool)
            then 128
            else 64
          let elements : Int :=
            (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
          let poly : Bool := (U == 1#1)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product
            (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            poly)))


def decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((U == 1#1) && (size != 0b00#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b11#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let datasize : Int :=
            if ((Q == 1#1) : Bool)
            then 128
            else 64
          let elements : Int :=
            (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
          let poly : Bool := (U == 1#1)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product
            (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            poly)))


def decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4671) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4672) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_not (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) esize
    (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
