module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0143
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0164
public import ArmFull.Fn.M0165
public import ArmFull.Fn.M0216
public import ArmFull.Fn.M0602
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866 set_option backward.proofsInPublic true @[expose] public section

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

def decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let source_is_sp ← (( do
        if ((Z == 0#1) : Bool)
        then
          (let source_is_sp : Bool :=
            if ((n == 31) : Bool)
            then true
            else source_is_sp
          (pure (source_is_sp)))
        else
          (do
            if ((n != 31) : Bool)
            then
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ())))
            else (pure (()))
            (pure (source_is_sp))) ) : SailM Bool )
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_pac_pacda_dp_1src (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) source_is_sp))


def decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let source_is_sp ← (( do
        if ((Z == 0#1) : Bool)
        then
          (let source_is_sp : Bool :=
            if ((n == 31) : Bool)
            then true
            else source_is_sp
          (pure (source_is_sp)))
        else
          (do
            if ((n != 31) : Bool)
            then
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ())))
            else (pure (()))
            (pure (source_is_sp))) ) : SailM Bool )
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_pac_pacdb_dp_1src (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) source_is_sp))


def decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let source_is_sp : Bool :=
        if ((m == 31) : Bool)
        then true
        else source_is_sp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_pac_pacga_dp_2src (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) source_is_sp))


def decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let source_is_sp ← (( do
        if ((Z == 0#1) : Bool)
        then
          (let source_is_sp : Bool :=
            if ((n == 31) : Bool)
            then true
            else source_is_sp
          (pure (source_is_sp)))
        else
          (do
            if ((n != 31) : Bool)
            then
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ())))
            else (pure (()))
            (pure (source_is_sp))) ) : SailM Bool )
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_pac_pacia_dp_1src (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) source_is_sp))


def decode_pacia_aarch64_instrs_integer_pac_pacia_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Int := 17
  let n : Int := 0
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0011000 =>
      (let d : Int := 30
      let n : Int := 31
      (pure ((d, n, source_is_sp))))
    | 0b0011001 =>
      (do
        let d : Int := 30
        let source_is_sp : Bool := true
        let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
        if (w__0 : Bool)
        then
          (do
            let w__1 ← (( do (BTypeCompatible_PACIXSP ()) ) : SailM Bool )
            (SetBTypeCompatible w__1))
        else (pure (()))
        (pure ((d, n, source_is_sp))))
    | 0b0001000 =>
      (let d : Int := 17
      let n : Int := 16
      (pure ((d, n, source_is_sp))))
    | 0b0001010 => sailThrow ((Error_See "PACIB"))
    | 0b0001100 => sailThrow ((Error_See "AUTIA"))
    | 0b0001110 => sailThrow ((Error_See "AUTIB"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001101#6 : (BitVec 6))) : Bool)
        then sailThrow ((Error_See "PACIB"))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001110#6 : (BitVec 6))) : Bool)
            then sailThrow ((Error_See "AUTIA"))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001111#6 : (BitVec 6))) : Bool)
                then sailThrow ((Error_See "AUTIB"))
                else
                  (do
                    match b__0 with
                    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
                    | _ => sailThrow ((Error_See "HINT")))))
        (pure ((d, n, source_is_sp)))) ) : SailM (Int × Int × Bool) )
  let n : Int := n
  let d : Int := d
  ArmFull.assert ((0 ≤b n) && (n ≤b 31)) "sail-inputs/26-armcert_c27.sail:247.43-247.44"
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_pac_pacia_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let source_is_sp ← (( do
        if ((Z == 0#1) : Bool)
        then
          (let source_is_sp : Bool :=
            if ((n == 31) : Bool)
            then true
            else source_is_sp
          (pure (source_is_sp)))
        else
          (do
            if ((n != 31) : Bool)
            then
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ())))
            else (pure (()))
            (pure (source_is_sp))) ) : SailM Bool )
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_pac_pacib_dp_1src (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) source_is_sp))


def decode_pacib_aarch64_instrs_integer_pac_pacib_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Int := 17
  let n : Int := 0
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0011010 =>
      (let d : Int := 30
      let n : Int := 31
      (pure ((d, n, source_is_sp))))
    | 0b0011011 =>
      (do
        let d : Int := 30
        let source_is_sp : Bool := true
        let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
        if (w__0 : Bool)
        then
          (do
            let w__1 ← (( do (BTypeCompatible_PACIXSP ()) ) : SailM Bool )
            (SetBTypeCompatible w__1))
        else (pure (()))
        (pure ((d, n, source_is_sp))))
    | 0b0001010 =>
      (let d : Int := 17
      let n : Int := 16
      (pure ((d, n, source_is_sp))))
    | 0b0001000 => sailThrow ((Error_See "PACIA"))
    | 0b0001100 => sailThrow ((Error_See "AUTIA"))
    | 0b0001110 => sailThrow ((Error_See "AUTIB"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001100#6 : (BitVec 6))) : Bool)
        then sailThrow ((Error_See "PACIA"))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001110#6 : (BitVec 6))) : Bool)
            then sailThrow ((Error_See "AUTIA"))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001111#6 : (BitVec 6))) : Bool)
                then sailThrow ((Error_See "AUTIB"))
                else
                  (do
                    match b__0 with
                    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
                    | _ => sailThrow ((Error_See "HINT")))))
        (pure ((d, n, source_is_sp)))) ) : SailM (Int × Int × Bool) )
  let n : Int := n
  let d : Int := d
  ArmFull.assert ((0 ≤b n) && (n ≤b 31)) "sail-inputs/26-armcert_c27.sail:302.43-302.44"
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_pac_pacib_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_rbit (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_rev_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
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
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (64))) ) : SailM Int )
  let container_size : Int := container_size
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_rev (Sail.Int.toNatChecked (container_size))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


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
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (64))) ) : SailM Int )
  let container_size : Int := container_size
  (__ArmCertEndOfDecode ())
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
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (64))) ) : SailM Int )
  let container_size : Int := container_size
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_rev (Sail.Int.toNatChecked (container_size))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_rmif_aarch64_instrs_integer_flags_rmif (mask : (BitVec 4)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (sf : (BitVec 1)) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (HaveFlagManipulateExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((sf != 1#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let lsb : Int := (BitVec.toNat imm6)
      let n : Int := (BitVec.toNat Rn)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_flags_rmif (Sail.Int.toNatChecked (lsb)) mask
        (Sail.Int.toNatChecked (n))))


def decode_rprfm_reg_aarch64_instrs_memory_single_general_range (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let operation : (BitVec 6) :=
    ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 2)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              option_name 0)]))) +++ S) +++ (Sail.BitVec.extractLsb Rt 2 0))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_single_general_range (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) operation)


def decode_sb_aarch64_instrs_system_barriers_sb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveSBExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_system_barriers_sb ()))


def decode_sdiv_aarch64_instrs_integer_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let is_unsigned : Bool := (o1 == 0#1)
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_div (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_setf_aarch64_instrs_integer_flags_setf (Rn : (BitVec 5)) (sz : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (HaveFlagManipulateExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((sf != 0#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let msb : Int :=
        if ((sz == 1#1) : Bool)
        then 15
        else 7
      let n : Int := (BitVec.toNat Rn)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_flags_setf (Sail.Int.toNatChecked (msb))
        (Sail.Int.toNatChecked (n))))


def decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Nat := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) datasize destsize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op is_unsigned)


def decode_smax_imm_aarch64_instrs_integer_arithmetic_max_min_smax_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let d : Int := (BitVec.toNat Rd)
      let imm : Int := (BitVec.toInt imm8)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_smax_imm (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) imm (Sail.Int.toNatChecked (n))))


def decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_smax_reg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_smc_aarch64_instrs_system_exceptions_runtime_smc (imm16 : (BitVec 16)) : SailM Unit := do
  let imm : (BitVec 16) := imm16
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_exceptions_runtime_smc imm)


def decode_smin_imm_aarch64_instrs_integer_arithmetic_max_min_smin_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let d : Int := (BitVec.toNat Rd)
      let imm : Int := (BitVec.toInt imm8)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_smin_imm (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) imm (Sail.Int.toNatChecked (n))))


def decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_smin_reg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Nat := 64
  let datasize : Int := destsize
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


end ArmFull.Functions
