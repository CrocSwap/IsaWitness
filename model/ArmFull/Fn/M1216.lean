module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1138
public import ArmFull.Fn.M1176 set_option backward.proofsInPublic true @[expose] public section

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

def decode_BFMLALT_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let index : Int := (BitVec.toNat (i3h +++ i3l))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLALT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLALT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLALT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLALT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLALT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFMLSLB_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let index : Int := (BitVec.toNat (i3h +++ i3l))
      let op1_neg : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLB_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLB_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLB_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLB_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op1_neg))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLB_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op1_neg))
      | _ => (pure (())))


def decode_BFMLSLT_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let index : Int := (BitVec.toNat (i3h +++ i3l))
      let op1_neg : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op1_neg))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMLSLT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da))
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op1_neg))
      | _ => (pure (())))


def decode_BFDOT_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFDOT_Z_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let index : Int := (BitVec.toNat i2)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFDOT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FDOT_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FDOT_Z_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let index : Int := (BitVec.toNat i2)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FDOT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFCVT_Z_P_Z_S2BF (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVT_Z_P_Z_S2BF 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVT_Z_P_Z_S2BF 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVT_Z_P_Z_S2BF 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVT_Z_P_Z_S2BF 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVT_Z_P_Z_S2BF 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFCVTNT_Z_P_Z_S2BF (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVTNT_Z_P_Z_S2BF 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVTNT_Z_P_Z_S2BF 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVTNT_Z_P_Z_S2BF 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVTNT_Z_P_Z_S2BF 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFCVTNT_Z_P_Z_S2BF 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMMLA_Z_ZZZ_S (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5156)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5157)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let addend ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5158)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5159)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op1 := (w__0 : (BitVec (4 * esize)))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op2 := (w__1 : (BitVec (4 * esize)))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let addend := (w__2 : (BitVec (4 * esize)))
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do (FPMatMulAdd addend op1 op2 esize w__3) ) : SailM (BitVec (4 * esize))
            )
          let res := (w__4 : (BitVec (4 * esize)))
          let w__5 ← (( do
            (Elem_set result s (Sail.Int.toNatChecked ((4 *i esize))) (Sail.BitVec.castWidth res)) )
            : SailM (BitVec VL) )
          let result := (w__5 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec VL))
    )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMMLA_Z_ZZZ_D (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b (esize *i 4)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5160)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5161)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let addend ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5162)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5163)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op1 := (w__0 : (BitVec (4 * esize)))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op2 := (w__1 : (BitVec (4 * esize)))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let addend := (w__2 : (BitVec (4 * esize)))
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do (FPMatMulAdd addend op1 op2 esize w__3) ) : SailM (BitVec (4 * esize))
            )
          let res := (w__4 : (BitVec (4 * esize)))
          let w__5 ← (( do
            (Elem_set result s (Sail.Int.toNatChecked ((4 *i esize))) (Sail.BitVec.castWidth res)) )
            : SailM (BitVec VL) )
          let result := (w__5 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec VL))
    )
  (Z_set da VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
