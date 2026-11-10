import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0937
import ArmFull.Fn.M0938
import ArmFull.Fn.M0951
import ArmFull.Fn.M0952

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

def decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := 0
  let b__0 := (Q +++ imm5)
  let size ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
             b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
    then (pure (0))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
        then (pure (1))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     b__0 2 0)) == (0b100#3 : (BitVec 3)))) : Bool)
            then (pure (2))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 5 5)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         b__0 3 0)) == (0x8#4 : (BitVec 4)))) : Bool)
                then (pure (3))
                else sailThrow ((Error_Undefined ()))))) ) : SailM Int )
  let size : Int := size
  let idxdsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])) == 1#1) : Bool)
    then 128
    else 64
  let index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
  let esize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (size)))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  (execute_aarch64_instrs_vector_transfer_integer_move_unsigned (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) index (Sail.Int.toNatChecked (n)))


def decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (n)))


def decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (n)))


def decode_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let part : Int := (BitVec.toNat op)
  (execute_aarch64_instrs_vector_transfer_vector_permute_unzip (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)))


def decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let part : Int := (BitVec.toNat op)
  (execute_aarch64_instrs_vector_transfer_vector_permute_unzip (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)))


def decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat (Sail.Int.toNatChecked (d)) datasize
    elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)))


def decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let part : Int := (BitVec.toNat op)
  let pairs : Int := (Int.ediv (Sail.Int.toNatChecked (elements)) 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_zip (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pairs (Sail.Int.toNatChecked (part)))


def decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let part : Int := (BitVec.toNat op)
  let pairs : Int := (Int.ediv (Sail.Int.toNatChecked (elements)) 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_zip (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pairs (Sail.Int.toNatChecked (part)))


def decode_FEXPA_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FEXPA_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FEXPA_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FEXPA_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FEXPA_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FEXPA_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADR_Z_AZ_D_u32_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let osize : Nat := 32
  let is_unsigned : Bool := true
  let mbytes : Int := (Int.shiftl 1 (BitVec.toNat msz))
  match VL with
  | 128 =>
    (do
      (execute_ADR_Z_AZ_D_u32_scaled 128 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 256 =>
    (do
      (execute_ADR_Z_AZ_D_u32_scaled 256 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 512 =>
    (do
      (execute_ADR_Z_AZ_D_u32_scaled 512 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 1024 =>
    (do
      (execute_ADR_Z_AZ_D_u32_scaled 1024 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 2048 =>
    (do
      (execute_ADR_Z_AZ_D_u32_scaled 2048 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | _ => (pure (()))


def decode_ADR_Z_AZ_D_s32_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let osize : Nat := 32
  let is_unsigned : Bool := false
  let mbytes : Int := (Int.shiftl 1 (BitVec.toNat msz))
  match VL with
  | 128 =>
    (do
      (execute_ADR_Z_AZ_D_s32_scaled 128 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 256 =>
    (do
      (execute_ADR_Z_AZ_D_s32_scaled 256 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 512 =>
    (do
      (execute_ADR_Z_AZ_D_s32_scaled 512 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 1024 =>
    (do
      (execute_ADR_Z_AZ_D_s32_scaled 1024 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | 2048 =>
    (do
      (execute_ADR_Z_AZ_D_s32_scaled 2048 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes)) (Sail.Int.toNatChecked (n))
        osize is_unsigned))
  | _ => (pure (()))


def decode_ADR_Z_AZ_SD_same_scaled (sz : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let osize : Int := esize
  let is_unsigned : Bool := true
  let mbytes : Int := (Int.shiftl 1 (BitVec.toNat msz))
  match VL with
  | 128 =>
    (do
      (execute_ADR_Z_AZ_SD_same_scaled 128 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (osize)) is_unsigned))
  | 256 =>
    (do
      (execute_ADR_Z_AZ_SD_same_scaled 256 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (osize)) is_unsigned))
  | 512 =>
    (do
      (execute_ADR_Z_AZ_SD_same_scaled 512 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (osize)) is_unsigned))
  | 1024 =>
    (do
      (execute_ADR_Z_AZ_SD_same_scaled 1024 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (osize)) is_unsigned))
  | 2048 =>
    (do
      (execute_ADR_Z_AZ_SD_same_scaled 2048 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (mbytes))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (osize)) is_unsigned))
  | _ => (pure (()))


def decode_TRN1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let part : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_TRN1_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 256 =>
    (do
      (execute_TRN1_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 512 =>
    (do
      (execute_TRN1_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 1024 =>
    (do
      (execute_TRN1_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 2048 =>
    (do
      (execute_TRN1_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | _ => (pure (()))


def decode_TRN2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let part : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_TRN2_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 256 =>
    (do
      (execute_TRN2_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 512 =>
    (do
      (execute_TRN2_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 1024 =>
    (do
      (execute_TRN2_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 2048 =>
    (do
      (execute_TRN2_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | _ => (pure (()))


def decode_ZIP1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let part : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_ZIP1_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 256 =>
    (do
      (execute_ZIP1_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 512 =>
    (do
      (execute_ZIP1_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 1024 =>
    (do
      (execute_ZIP1_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 2048 =>
    (do
      (execute_ZIP1_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | _ => (pure (()))


def decode_ZIP2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let part : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_ZIP2_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 256 =>
    (do
      (execute_ZIP2_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 512 =>
    (do
      (execute_ZIP2_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 1024 =>
    (do
      (execute_ZIP2_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 2048 =>
    (do
      (execute_ZIP2_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | _ => (pure (()))


def decode_UZP1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let part : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_UZP1_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 256 =>
    (do
      (execute_UZP1_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 512 =>
    (do
      (execute_UZP1_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 1024 =>
    (do
      (execute_UZP1_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 2048 =>
    (do
      (execute_UZP1_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | _ => (pure (()))


def decode_UZP2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let part : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UZP2_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 256 =>
    (do
      (execute_UZP2_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 512 =>
    (do
      (execute_UZP2_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 1024 =>
    (do
      (execute_UZP2_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | 2048 =>
    (do
      (execute_UZP2_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) part))
  | _ => (pure (()))


def decode_COMPACT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((let b__0 := size
     (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_COMPACT_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_COMPACT_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_COMPACT_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_COMPACT_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_COMPACT_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
