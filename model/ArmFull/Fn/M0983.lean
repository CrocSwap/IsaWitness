module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0894
public import ArmFull.Fn.M0895 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SQINCW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCW_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCW_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCW_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCW_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCW_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_SQINCD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCD_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCD_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCD_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCD_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQINCD_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_UQDECH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 16
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECH_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECH_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECH_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECH_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECH_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_UQDECW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECW_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECW_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECW_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECW_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECW_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_UQDECD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECD_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECD_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECD_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECD_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQDECD_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_SQDECH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 16
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECH_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECH_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECH_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECH_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECH_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_SQDECW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECW_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECW_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECW_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECW_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECW_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_SQDECD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let dn : Int := (BitVec.toNat Zdn)
      let pat : (BitVec 5) := pattern
      let imm : Int := ((BitVec.toNat imm4) +i 1)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECD_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECD_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECD_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECD_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQDECD_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (imm)) pat is_unsigned))
      | _ => (pure (())))


def decode_CTERMEQ_RR__ (sz : (BitVec 1)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (ne : (BitVec 1)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let op : SVECmp := Cmp_EQ
      (__ArmCertEndOfDecode ())
      (execute_CTERMEQ_RR__ (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op))


def decode_CTERMNE_RR__ (sz : (BitVec 1)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (ne : (BitVec 1)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let op : SVECmp := Cmp_NE
      (__ArmCertEndOfDecode ())
      (execute_CTERMNE_RR__ (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op))


def decode_FDUP_Z_I__ (size : (BitVec 2)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let d : Int := (BitVec.toNat Zd)
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:23403.45-23403.46"
          let imm ← (( do
            ((Sail.BitVec.castWidth ) <$> (VFPExpandImm imm8 (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FDUP_Z_I__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.BitVec.castWidth imm)))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FDUP_Z_I__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.BitVec.castWidth imm)))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FDUP_Z_I__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.BitVec.castWidth imm)))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FDUP_Z_I__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.BitVec.castWidth imm)))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FDUP_Z_I__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.BitVec.castWidth imm)))
          | _ => (pure (()))))


def decode_FCPY_Z_P_I__ (size : (BitVec 2)) (Pg : (BitVec 4)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let d : Int := (BitVec.toNat Zd)
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:23466.45-23466.46"
          let imm ← (( do
            ((Sail.BitVec.castWidth ) <$> (VFPExpandImm imm8 (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCPY_Z_P_I__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCPY_Z_P_I__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCPY_Z_P_I__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCPY_Z_P_I__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCPY_Z_P_I__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.BitVec.castWidth imm)))
          | _ => (pure (()))))


def decode_DUP_Z_I__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let imm : Int := (BitVec.toInt imm8)
          let imm : Int :=
            if ((sh == 1#1) : Bool)
            then (Int.shiftl imm 8)
            else imm
          let imm : Int := imm
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_DUP_Z_I__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_DUP_Z_I__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_DUP_Z_I__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_DUP_Z_I__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                imm))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_DUP_Z_I__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                imm))
          | _ => (pure (()))))


end ArmFull.Functions
