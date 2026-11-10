import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0086
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0178
import ArmFull.Fn.M1079
import ArmFull.Fn.M1080

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

def decode_rcwsclrp_aarch64_instrs_memory_rcws_ld_128_rcwsclrp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_128_rcwsclrp acquire (Sail.Int.toNatChecked (n)) op release
    soft (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_rcwset_aarch64_instrs_memory_rcw_ld_rcwset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_rcwset acquire (Sail.Int.toNatChecked (n)) op release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwsetp_aarch64_instrs_memory_rcw_ld_128_rcwsetp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_128_rcwsetp acquire (Sail.Int.toNatChecked (n)) op release
    soft (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_rcwsset_aarch64_instrs_memory_rcws_ld_rcwsset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_rcwsset acquire (Sail.Int.toNatChecked (n)) op release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwssetp_aarch64_instrs_memory_rcws_ld_128_rcwssetp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_128_rcwssetp acquire (Sail.Int.toNatChecked (n)) op release
    soft (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_rcwsswp_aarch64_instrs_memory_rcws_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_swp acquire (Sail.Int.toNatChecked (n)) release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwsswpp_aarch64_instrs_memory_rcws_swp_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_swp_128 acquire (Sail.Int.toNatChecked (n)) release soft
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_rcwswp_aarch64_instrs_memory_rcw_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_swp acquire (Sail.Int.toNatChecked (n)) release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwswpp_aarch64_instrs_memory_rcw_swp_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_swp_128 acquire (Sail.Int.toNatChecked (n)) release soft
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int := esize
  let elements : Nat := 1
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int := esize
  let elements : Nat := 1
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b (Rt : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatLS64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb Rt 4 3)) == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             Rt 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_STORE
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64b
  (execute_aarch64_instrs_memory_atomicops_st_acc_st64b lst memop (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatLS64_V ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb Rt 4 3)) == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             Rt 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_STORE
  let s : Int := (BitVec.toNat Rs)
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64bv
  (execute_aarch64_instrs_memory_atomicops_st_acc_st64bv Rs lst memop (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) tagchecked)


def decode_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatLS64_ACCDATA ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb Rt 4 3)) == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             Rt 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_STORE
  let s : Int := (BitVec.toNat Rs)
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64bv0
  (execute_aarch64_instrs_memory_atomicops_st_acc_st64bv0 Rs lst memop (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) tagchecked)


def decode_swp_aarch64_instrs_memory_atomicops_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_swpb_aarch64_instrs_memory_atomicops_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_swph_aarch64_instrs_memory_atomicops_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


end ArmFull.Functions
