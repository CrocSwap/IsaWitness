import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0152
import ArmFull.Fn.M0165
import ArmFull.Fn.M0166

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

def decode_rev16_int_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let container_size : Int := 16
  let container_size ← (( do
    match opc with
    | 0b00 =>
      (do
        (Unreachable ())
        (pure (container_size)))
    | 0b01 => (pure (16))
    | 0b10 => (pure (32))
    | _ =>
      (do
        if ((sf == 0#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (64))) ) : SailM Int )
  let container_size : Int := container_size
  (execute_aarch64_instrs_integer_arithmetic_rev (Sail.Int.toNatChecked (container_size))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_rev32_int_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let container_size : Int := 16
  let container_size ← (( do
    match opc with
    | 0b00 =>
      (do
        (Unreachable ())
        (pure (container_size)))
    | 0b01 => (pure (16))
    | 0b10 => (pure (32))
    | _ =>
      (do
        if ((sf == 0#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (64))) ) : SailM Int )
  let container_size : Int := container_size
  (execute_aarch64_instrs_integer_arithmetic_rev (Sail.Int.toNatChecked (container_size))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_rmif_aarch64_instrs_integer_flags_rmif (mask : (BitVec 4)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (sf : (BitVec 1)) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (HaveFlagManipulateExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((sf != 1#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let lsb : Int := (BitVec.toNat imm6)
  let n : Int := (BitVec.toNat Rn)
  (execute_aarch64_instrs_integer_flags_rmif (Sail.Int.toNatChecked (lsb)) mask
    (Sail.Int.toNatChecked (n)))


def decode_rprfm_reg_aarch64_instrs_memory_single_general_range (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let operation : (BitVec 6) :=
    ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 2)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              option_name 0)]))) +++ S) +++ (Sail.BitVec.extractLsb Rt 2 0))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_memory_single_general_range (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) operation)


def decode_sdiv_aarch64_instrs_integer_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let is_unsigned : Bool := (o1 == 0#1)
  (execute_aarch64_instrs_integer_arithmetic_div (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_udiv_aarch64_instrs_integer_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let is_unsigned : Bool := (o1 == 0#1)
  (execute_aarch64_instrs_integer_arithmetic_div (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_setf_aarch64_instrs_integer_flags_setf (Rn : (BitVec 5)) (sz : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (HaveFlagManipulateExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((sf != 0#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let msb : Int :=
    if ((sz == 1#1) : Bool)
    then 15
    else 7
  let n : Int := (BitVec.toNat Rn)
  (execute_aarch64_instrs_integer_flags_setf (Sail.Int.toNatChecked (msb))
    (Sail.Int.toNatChecked (n)))


def decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Nat := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) datasize destsize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op is_unsigned)


def decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Nat := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) datasize destsize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op is_unsigned)


def decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Nat := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) datasize destsize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op is_unsigned)


def decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Nat := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) datasize destsize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op is_unsigned)


def decode_smax_imm_aarch64_instrs_integer_arithmetic_max_min_smax_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smax_imm (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) imm (Sail.Int.toNatChecked (n)))


def decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smax_reg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_smin_imm_aarch64_instrs_integer_arithmetic_max_min_smin_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smin_imm (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) imm (Sail.Int.toNatChecked (n)))


def decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smin_reg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Int := destsize
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Int := destsize
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Xd)
  let n : Int := (BitVec.toNat Xn)
  let m : Int := (BitVec.toNat Xm)
  let setflags : Bool := false
  (execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags)


def decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Xd)
  let n : Int := (BitVec.toNat Xn)
  let m : Int := (BitVec.toNat Xm)
  let setflags : Bool := true
  (execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags)


def decode_umax_imm_aarch64_instrs_integer_arithmetic_max_min_umax_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toNat imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umax_imm (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)))


def decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umax_reg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umin_reg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_umin_imm_aarch64_instrs_integer_arithmetic_max_min_umin_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toNat imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umin_imm (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)))


def __UNKNOWN_AddressDescriptor (_ : Unit) : SailM AddressDescriptor := do
  (undefined_AddressDescriptor (← occLabel 388) ())


def __UNKNOWN_TLBLine (_ : Unit) : SailM TLBLine := do
  (undefined_TLBLine (← occLabel 468) ())


def IsSecureBelowEL3 (_ : Unit) : SailM Bool := do
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_SCRType_NS w__0) == 0#1))))
  else
    (do
      let w__4 ← (( do
        if (((HaveEL EL2) : Bool) : Bool)
        then
          (do
            if ((← do
                 let w__1 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__2 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                (pure (((! w__2) : Bool)))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then (pure (false))
      else
        (do
          (__IMPDEF_boolean "Secure-only implementation")))


def __get_FPCR (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : FPCR_Type := value_name
  let tmp : FPCR_Type := (Mk_FPCR_Type (tmp &&& (Complement.complement 0xFFFFFFFFF80040F8#64)))
  let w__0 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else tmp
  let w__1 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 64) :=
    if ((! w__1) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else tmp
  let w__2 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__2) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else tmp
  let w__3 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  let tmp : (BitVec 64) :=
    if ((! w__3) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else tmp
  let w__4 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__4) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000#16 64)))))
    else tmp
  let w__5 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 64) :=
    if ((! w__5) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000#16 64)))))
    else tmp
  let w__6 ← (( do (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ") ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__6 : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x370000#24 64)))))
    else tmp
  (pure (tmp))


def __get_FPSCR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : FPSCR_Type := value_name
  let tmp : FPSCR_Type :=
    (Mk_FPSCR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x6060#16 32)))))
  let w__0 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100#12 32)))))
    else tmp
  let w__1 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 32) :=
    if ((! w__1) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200#12 32)))))
    else tmp
  let w__2 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__2) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400#12 32)))))
    else tmp
  let w__3 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  let tmp : (BitVec 32) :=
    if ((! w__3) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800#12 32)))))
    else tmp
  let w__4 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__4) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000#16 32)))))
    else tmp
  let w__5 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 32) :=
    if ((! w__5) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000#16 32)))))
    else tmp
  let w__6 ← (( do (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if (w__6 : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x370000#24 32)))))
    else tmp
  (pure (tmp))


def ImpDefInt (x : String) : SailM Int := do
  if ((x == "Number of breakpoints") : Bool)
  then
    (do
      (getNumBreakpoints ()))
  else
    (do
      if ((x == "Number of watchpoints") : Bool)
      then
        (do
          (getNumWatchpoints ()))
      else
        (do
          if ((x == "Number of event counters") : Bool)
          then
            (do
              readReg NUM_PMU_COUNTERS)
          else
            (do
              if ((x == "Number of context-aware breakpoints") : Bool)
              then
                (do
                  (getNumCtxBreakpoints ()))
              else
                (do
                  if ((x == "Max implemented VL") : Bool)
                  then
                    (do
                      readReg __max_implemented_sveveclen)
                  else
                    (do
                      if ((x == "Maximum bytes used in a single block of a copy") : Bool)
                      then (pure (1))
                      else
                        (do
                          if ((x == "Number of BRB records") : Bool)
                          then
                            (do
                              readReg NUM_BRBE_RECORDS)
                          else
                            (do
                              if ((x == "SPE Events packet payload size") : Bool)
                              then (pure (4))
                              else
                                (do
                                  if ((x == "SPE Data Source packet payload size") : Bool)
                                  then (pure (2))
                                  else
                                    (do
                                      if ((x == "Reserved Intermediate Physical Address size value") : Bool)
                                      then (pure (52))
                                      else
                                        (do
                                          if ((x == "Maximum Physical Address Size") : Bool)
                                          then
                                            (do
                                              readReg __supported_pa_size)
                                          else
                                            (do
                                              if ((x == "Block BBM support level") : Bool)
                                              then
                                                (do
                                                  readReg __block_bbm_implemented)
                                              else
                                                (do
                                                  if ((x == "SVE Extended BFloat16 instructions are implemented") : Bool)
                                                  then
                                                    (do
                                                      readReg __has_sve_extended_bf16)
                                                  else
                                                    (do
                                                      if ((x == "Max implemented SVL") : Bool)
                                                      then
                                                        (do
                                                          readReg __max_implemented_smeveclen)
                                                      else
                                                        (do
                                                          if ((x == "Data Cache Invalidate Watchpoint Size") : Bool)
                                                          then
                                                            (do
                                                              let w__10 ← (( do readReg CTR_EL0 )
                                                                : SailM (BitVec 64) )
                                                              (pure ((4 *i (2 ^i (BitVec.toNat
                                                                      (_get_CTR_EL0_Type_DminLine
                                                                        w__10)))))))
                                                          else
                                                            (do
                                                              if ((x == "Instruction Cache Invalidate by VA Size") : Bool)
                                                              then
                                                                (do
                                                                  let w__11 ← (( do
                                                                    readReg CTR_EL0 ) : SailM
                                                                    (BitVec 64) )
                                                                  (pure ((4 *i (2 ^i (BitVec.toNat
                                                                          (_get_CTR_EL0_Type_DminLine
                                                                            w__11)))))))
                                                              else
                                                                (do
                                                                  if ((x == "Linesize for DC SW instructions") : Bool)
                                                                  then
                                                                    (do
                                                                      let w__12 ← (( do
                                                                        readReg CTR_EL0 ) : SailM
                                                                        (BitVec 64) )
                                                                      (pure ((4 *i (2 ^i (BitVec.toNat
                                                                              (_get_CTR_EL0_Type_DminLine
                                                                                w__12)))))))
                                                                  else
                                                                    (do
                                                                      if ((x == "Associativity for DC SW instructions") : Bool)
                                                                      then (pure (2))
                                                                      else
                                                                        (do
                                                                          if ((x == "Numsets for DC SW instructions") : Bool)
                                                                          then (pure (2))
                                                                          else
                                                                            (do
                                                                              let _ : Unit :=
                                                                                (print_endline
                                                                                  (String.append x
                                                                                    " is an unrecognized Implementation defined bit."))
                                                                              ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:746.20-746.21"
                                                                              throw Error.Exit)))))))))))))))))))


end ArmFull.Functions
