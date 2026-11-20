module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1129 set_option backward.proofsInPublic true @[expose] public section

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

def decode_fcvtps_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4217) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4218) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4219) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (128)))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__1 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__3 ← (( do (FPRoundingMode w__2) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            let (op, part) ← (( do
              if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 0
                (pure ((op, part)))) ) : SailM (FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            let (fltsize, op, part) ← (( do
              if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 1
                let fltsize : Int := 64
                (pure ((fltsize, op, part)))) ) : SailM (Int × FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__4 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            let (is_unsigned, op, rounding) ← (( do
              if ((! w__4) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let rounding : FPRounding := FPRounding_ZERO
                let is_unsigned : Bool :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                (pure ((is_unsigned, op, rounding)))) ) : SailM (Bool × FPConvOp × FPRounding) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "sail-inputs/15-instrs64.sail:15060.22-15060.23"
      throw Error.Exit)


def decode_fcvtpu_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4220) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4221) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4222) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (128)))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__1 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__3 ← (( do (FPRoundingMode w__2) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            let (op, part) ← (( do
              if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 0
                (pure ((op, part)))) ) : SailM (FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            let (fltsize, op, part) ← (( do
              if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 1
                let fltsize : Int := 64
                (pure ((fltsize, op, part)))) ) : SailM (Int × FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__4 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            let (is_unsigned, op, rounding) ← (( do
              if ((! w__4) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let rounding : FPRounding := FPRounding_ZERO
                let is_unsigned : Bool :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                (pure ((is_unsigned, op, rounding)))) ) : SailM (Bool × FPConvOp × FPRounding) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "sail-inputs/15-instrs64.sail:15170.22-15170.23"
      throw Error.Exit)


def decode_fcvtzs_float_int_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4223) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4224) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4225) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (128)))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__1 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__3 ← (( do (FPRoundingMode w__2) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            let (op, part) ← (( do
              if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 0
                (pure ((op, part)))) ) : SailM (FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            let (fltsize, op, part) ← (( do
              if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 1
                let fltsize : Int := 64
                (pure ((fltsize, op, part)))) ) : SailM (Int × FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__4 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            let (is_unsigned, op, rounding) ← (( do
              if ((! w__4) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let rounding : FPRounding := FPRounding_ZERO
                let is_unsigned : Bool :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                (pure ((is_unsigned, op, rounding)))) ) : SailM (Bool × FPConvOp × FPRounding) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "sail-inputs/15-instrs64.sail:15280.22-15280.23"
      throw Error.Exit)


def decode_fcvtzu_float_int_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4226) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4227) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4228) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (128)))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__1 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__3 ← (( do (FPRoundingMode w__2) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            let (op, part) ← (( do
              if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 0
                (pure ((op, part)))) ) : SailM (FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            let (fltsize, op, part) ← (( do
              if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 1
                let fltsize : Int := 64
                (pure ((fltsize, op, part)))) ) : SailM (Int × FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__4 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            let (is_unsigned, op, rounding) ← (( do
              if ((! w__4) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let rounding : FPRounding := FPRounding_ZERO
                let is_unsigned : Bool :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                (pure ((is_unsigned, op, rounding)))) ) : SailM (Bool × FPConvOp × FPRounding) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "sail-inputs/15-instrs64.sail:15390.22-15390.23"
      throw Error.Exit)


def decode_fjcvtzs_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4229) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4230) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4231) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (128)))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__1 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__3 ← (( do (FPRoundingMode w__2) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            let (op, part) ← (( do
              if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 0
                (pure ((op, part)))) ) : SailM (FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            let (fltsize, op, part) ← (( do
              if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 1
                let fltsize : Int := 64
                (pure ((fltsize, op, part)))) ) : SailM (Int × FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__4 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            let (is_unsigned, op, rounding) ← (( do
              if ((! w__4) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let rounding : FPRounding := FPRounding_ZERO
                let is_unsigned : Bool :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                (pure ((is_unsigned, op, rounding)))) ) : SailM (Bool × FPConvOp × FPRounding) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "sail-inputs/15-instrs64.sail:15500.22-15500.23"
      throw Error.Exit)


end ArmFull.Functions
