module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0885
public import ArmFull.Fn.M0886 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SUB_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((size +++ sh) == 0b001#3) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let dn : Int := (BitVec.toNat Zdn)
          let imm : Int := (BitVec.toNat imm8)
          let imm : Int :=
            if ((sh == 1#1) : Bool)
            then (Int.shiftl imm 8)
            else imm
          let imm : Int := imm
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUB_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUB_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUB_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUB_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUB_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | _ => (pure (()))))


def decode_SUBR_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((size +++ sh) == 0b001#3) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let dn : Int := (BitVec.toNat Zdn)
          let imm : Int := (BitVec.toNat imm8)
          let imm : Int :=
            if ((sh == 1#1) : Bool)
            then (Int.shiftl imm 8)
            else imm
          let imm : Int := imm
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUBR_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUBR_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUBR_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUBR_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUBR_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
                imm))
          | _ => (pure (()))))


def decode_MUL_Z_ZI__ (size : (BitVec 2)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let dn : Int := (BitVec.toNat Zdn)
      let imm : Int := (BitVec.toInt imm8)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_MUL_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_MUL_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_MUL_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_MUL_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_MUL_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
      | _ => (pure (())))


def decode_UMAX_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let dn : Int := (BitVec.toNat Zdn)
      let is_unsigned : Bool := true
      let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | _ => (pure (())))


def decode_SMAX_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let dn : Int := (BitVec.toNat Zdn)
      let is_unsigned : Bool := false
      let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | _ => (pure (())))


def decode_UMIN_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let dn : Int := (BitVec.toNat Zdn)
      let is_unsigned : Bool := true
      let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | _ => (pure (())))


def decode_SMIN_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let dn : Int := (BitVec.toNat Zdn)
      let is_unsigned : Bool := false
      let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
            is_unsigned))
      | _ => (pure (())))


def decode_ADDPL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Rn)
      let d : Int := (BitVec.toNat Rd)
      let imm : Int := (BitVec.toInt imm6)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDPL_R_RI__ 128 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDPL_R_RI__ 256 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDPL_R_RI__ 512 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDPL_R_RI__ 1024 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDPL_R_RI__ 2048 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ADDVL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Rn)
      let d : Int := (BitVec.toNat Rd)
      let imm : Int := (BitVec.toInt imm6)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDVL_R_RI__ 128 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDVL_R_RI__ 256 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDVL_R_RI__ 512 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDVL_R_RI__ 1024 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADDVL_R_RI__ 2048 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          (execute_ADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_AND_Z_ZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BIC_Z_ZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


end ArmFull.Functions
