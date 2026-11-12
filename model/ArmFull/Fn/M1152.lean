import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0086
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1105
import ArmFull.Fn.M1108
import ArmFull.Fn.M1111

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

def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)))


def decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let abs : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd abs
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let abs : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd abs
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_FADD_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:79.49-79.50"
        ((Sail.BitVec.castWidth ) <$> (FPPointFive 0#1 (Sail.Int.toNatChecked (esize)))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:82.49-82.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FADD_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FADD_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FADD_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FADD_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FADD_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FSUB_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:152.49-152.50"
        ((Sail.BitVec.castWidth ) <$> (FPPointFive 0#1 (Sail.Int.toNatChecked (esize)))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:155.49-155.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FSUB_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FSUB_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FSUB_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FSUB_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FSUB_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FMUL_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:225.49-225.50"
        ((Sail.BitVec.castWidth ) <$> (FPPointFive 0#1 (Sail.Int.toNatChecked (esize)))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:228.49-228.50"
        ((Sail.BitVec.castWidth ) <$> (FPTwo 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FMUL_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FMUL_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FMUL_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FMUL_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FMUL_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FSUBR_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:298.49-298.50"
        ((Sail.BitVec.castWidth ) <$> (FPPointFive 0#1 (Sail.Int.toNatChecked (esize)))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:301.49-301.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FSUBR_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FSUBR_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FSUBR_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FSUBR_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FSUBR_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FMAXNM_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (esize)))))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:371.49-371.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FMAXNM_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FMAXNM_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FMAXNM_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FMAXNM_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FMAXNM_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FMINNM_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (esize)))))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:441.49-441.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FMINNM_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FMINNM_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FMINNM_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FMINNM_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FMINNM_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FMAX_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (esize)))))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:511.49-511.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FMAX_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FMAX_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FMAX_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FMAX_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FMAX_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FMIN_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (esize)))))))
    else
      (do
        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:581.49-581.50"
        ((Sail.BitVec.castWidth ) <$> (FPOne 0#1 (Sail.Int.toNatChecked (esize))))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  match VL with
  | 128 =>
    (do
      (execute_FMIN_Z_P_ZS__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 256 =>
    (do
      (execute_FMIN_Z_P_ZS__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 512 =>
    (do
      (execute_FMIN_Z_P_ZS__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 1024 =>
    (do
      (execute_FMIN_Z_P_ZS__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | 2048 =>
    (do
      (execute_FMIN_Z_P_ZS__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
  | _ => (pure (()))


def decode_FADDA_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Vdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Vdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FADDA_V_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FADDA_V_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FADDA_V_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FADDA_V_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FADDA_V_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


end ArmFull.Functions
