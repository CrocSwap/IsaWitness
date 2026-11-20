module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0921
public import ArmFull.Fn.M0922 set_option backward.proofsInPublic true @[expose] public section

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

def decode_WHILEHI_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_GT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_WHILEHS_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_GE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_WHILEGT_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_GT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_WHILEGE_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_GE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_SQRSHRN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 1)) (imm4 : (BitVec 4)) (U : (BitVec 1)) (R : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := (esize -i (BitVec.toNat imm4))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))


def decode_SQRSHRUN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 1)) (imm4 : (BitVec 4)) (U : (BitVec 1)) (R : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := (esize -i (BitVec.toNat imm4))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRUN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRUN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRUN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRUN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRUN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))


def decode_UQRSHRN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 1)) (imm4 : (BitVec 4)) (U : (BitVec 1)) (R : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := (esize -i (BitVec.toNat imm4))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHRN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHRN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHRN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHRN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHRN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))


def decode_SQCVTN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQCVTUN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UQCVTN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_DUPQ_Z_Zi__ (i1 : (BitVec 1)) (tsz : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let imm : (BitVec 5) := (i1 +++ tsz)
      let esize : Int := 8
      let index ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 5719) 0 15))) ) :
        SailM Nat )
      let (esize, index) ← (( do
        match tsz with
        | 0b0000 =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | 0b1000 =>
          (let esize : Int := 64
          let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 4))
          (pure ((esize, index))))
        | b__0 =>
          (let (esize, index) : (Int × Nat) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 2 0)) == (0b100#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 32
              let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 3))
              (esize, index))
            else
              (let (esize, index) : (Int × Nat) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 1 0)) == (0b10#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 16
                  let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 2))
                  (esize, index))
                else
                  (let esize : Int := 8
                  let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 1))
                  (esize, index))
              (esize, index))
          (pure ((esize, index)))) ) : SailM (Int × Nat) )
      let index : Int := index
      let esize : Int := esize
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_DUPQ_Z_Zi__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_DUPQ_Z_Zi__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_DUPQ_Z_Zi__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_DUPQ_Z_Zi__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_DUPQ_Z_Zi__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


end ArmFull.Functions
