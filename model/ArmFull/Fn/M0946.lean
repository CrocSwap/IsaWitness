import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M0863
import ArmFull.Fn.M0864

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

def decode_UQDECW_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize : Nat := 32
  (execute_UQDECW_R_RS_UW (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_UQDECD_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize : Nat := 32
  (execute_UQDECD_R_RS_UW (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECB_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 32
  (execute_SQDECB_R_RS_SX (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECH_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 32
  (execute_SQDECH_R_RS_SX (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECW_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 32
  (execute_SQDECW_R_RS_SX (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECD_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 32
  (execute_SQDECD_R_RS_SX (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_UQDECB_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize : Nat := 64
  (execute_UQDECB_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_UQDECH_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize : Nat := 64
  (execute_UQDECH_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_UQDECW_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize : Nat := 64
  (execute_UQDECW_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_UQDECD_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize : Nat := 64
  (execute_UQDECD_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECB_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 64
  (execute_SQDECB_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECH_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 64
  (execute_SQDECH_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECW_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 64
  (execute_SQDECW_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_SQDECD_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize : Nat := 64
  (execute_SQDECD_R_RS_X (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat ssize
    is_unsigned)


def decode_CNTB_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let d : Int := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  (execute_CNTB_R_S__ (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm)) pat)


def decode_CNTH_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let d : Int := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  (execute_CNTH_R_S__ (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm)) pat)


def decode_CNTW_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let d : Int := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  (execute_CNTW_R_S__ (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm)) pat)


def decode_CNTD_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let d : Int := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  (execute_CNTD_R_S__ (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm)) pat)


def decode_DECH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let dn : Int := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_DECH_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_DECH_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_DECH_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_DECH_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_DECH_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


def decode_DECW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let dn : Int := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_DECW_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_DECW_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_DECW_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_DECW_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_DECW_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


def decode_DECD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let dn : Int := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_DECD_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_DECD_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_DECD_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_DECD_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_DECD_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


def decode_INCH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let dn : Int := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_INCH_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_INCH_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_INCH_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_INCH_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_INCH_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


def decode_INCW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let dn : Int := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_INCW_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_INCW_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_INCW_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_INCW_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_INCW_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


def decode_INCD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let dn : Int := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_INCD_Z_ZS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_INCD_Z_ZS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_INCD_Z_ZS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_INCD_Z_ZS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_INCD_Z_ZS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


end ArmFull.Functions
