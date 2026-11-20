module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0887
public import ArmFull.Fn.M0888 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SMAX_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | _ => (pure (())))


def decode_UMIN_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | _ => (pure (())))


def decode_SMIN_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | _ => (pure (())))


def decode_UMULH_Z_P_ZZ__ (size : (BitVec 2)) (H : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | _ => (pure (())))


def decode_SMULH_Z_P_ZZ__ (size : (BitVec 2)) (H : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) is_unsigned))
      | _ => (pure (())))


def decode_WHILELO_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_LT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_WHILELS_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_LE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_WHILELT_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_LT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_WHILELE_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_LE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_WHILEHI_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_GT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHI_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_WHILEHS_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_GE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEHS_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
