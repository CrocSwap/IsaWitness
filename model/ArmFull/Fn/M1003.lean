module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0908 set_option backward.proofsInPublic true @[expose] public section

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

def decode_UQXTNB_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let tsize : (BitVec 3) := (tszh +++ tszl)
      let esize : Int := 16
      let esize ← (( do
        match tsize with
        | 0b001 => (pure (16))
        | 0b010 => (pure (32))
        | 0b100 => (pure (64))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQXTUNB_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let tsize : (BitVec 3) := (tszh +++ tszl)
      let esize : Int := 16
      let esize ← (( do
        match tsize with
        | 0b001 => (pure (16))
        | 0b010 => (pure (32))
        | 0b100 => (pure (64))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQXTNT_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let tsize : (BitVec 3) := (tszh +++ tszl)
      let esize : Int := 16
      let esize ← (( do
        match tsize with
        | 0b001 => (pure (16))
        | 0b010 => (pure (32))
        | 0b100 => (pure (64))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTNT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTNT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTNT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTNT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTNT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UQXTNT_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let tsize : (BitVec 3) := (tszh +++ tszl)
      let esize : Int := 16
      let esize ← (( do
        match tsize with
        | 0b001 => (pure (16))
        | 0b010 => (pure (32))
        | 0b100 => (pure (64))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQXTNT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQXTUNT_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let tsize : (BitVec 3) := (tszh +++ tszl)
      let esize : Int := 16
      let esize ← (( do
        match tsize with
        | 0b001 => (pure (16))
        | 0b010 => (pure (32))
        | 0b100 => (pure (64))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQXTUNT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_SMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SMULLB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_UMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_UMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UMULLB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_SQDMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_SQDMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SQDMULLB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


end ArmFull.Functions
