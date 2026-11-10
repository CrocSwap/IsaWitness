import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0877

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

def decode_SQRSHRUNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b000 => sailThrow ((Error_Undefined ()))
    | 0b001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b01#2 : (BitVec 2))) : Bool)
        then 16
        else 32
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHRUNB_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_SQRSHRUNB_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_SQRSHRUNB_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_SQRSHRUNB_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_SQRSHRUNB_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_SQRSHRUNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b000 => sailThrow ((Error_Undefined ()))
    | 0b001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b01#2 : (BitVec 2))) : Bool)
        then 16
        else 32
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHRUNT_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_SQRSHRUNT_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_SQRSHRUNT_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_SQRSHRUNT_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_SQRSHRUNT_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_SRSHR_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b0000 => sailThrow ((Error_Undefined ()))
    | 0b0001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then 16
        else
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
          then 32
          else 64)
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SRSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:37602.22-37602.23"
      throw Error.Exit)


def decode_URSHR_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b0000 => sailThrow ((Error_Undefined ()))
    | 0b0001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then 16
        else
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
          then 32
          else 64)
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_URSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_URSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_URSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_URSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_URSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_URSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_URSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_URSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_URSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_URSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_URSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_URSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSHR_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_URSHR_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_URSHR_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_URSHR_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_URSHR_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:37755.22-37755.23"
      throw Error.Exit)


def decode_SQSHL_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b0000 => sailThrow ((Error_Undefined ()))
    | 0b0001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then 16
        else
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
          then 32
          else 64)
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let shift : Int := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_SQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:37908.22-37908.23"
      throw Error.Exit)


def decode_UQSHL_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b0000 => sailThrow ((Error_Undefined ()))
    | 0b0001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then 16
        else
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
          then 32
          else 64)
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let shift : Int := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 128 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 256 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 256 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 512 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 512 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 1024 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 1024 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | 2048 =>
        (do
          (execute_UQSHL_Z_P_ZI__ 2048 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (g))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:38061.22-38061.23"
      throw Error.Exit)


end ArmFull.Functions
