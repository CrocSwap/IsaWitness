import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1225
import ArmFull.Fn.M1226
import ArmFull.Fn.M1227

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

def decode_ST1D_Z_P_BR_U128 (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 128
  let msize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_ST1D_Z_P_BR_U128 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST1D_Z_P_BR_U128 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST1D_Z_P_BR_U128 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST1D_Z_P_BR_U128 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST1D_Z_P_BR_U128 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_STNT1B_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1B_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1B_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1B_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1B_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_STNT1H_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1H_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1H_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1H_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1H_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_STNT1W_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1W_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1W_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1W_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1W_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_STNT1D_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1D_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1D_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1D_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1D_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST2B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ST2B_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST2B_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST2B_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST2B_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST2B_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST2H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ST2H_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST2H_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST2H_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST2H_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST2H_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST2W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ST2W_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST2W_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST2W_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST2W_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST2W_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST2D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ST2D_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST2D_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST2D_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST2D_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST2D_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST3B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_ST3B_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST3B_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST3B_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST3B_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST3B_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST3H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_ST3H_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST3H_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST3H_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST3H_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST3H_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST3W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_ST3W_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST3W_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST3W_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST3W_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST3W_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST3D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_ST3D_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST3D_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST3D_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST3D_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST3D_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST4B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_ST4B_Z_P_BR_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST4B_Z_P_BR_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST4B_Z_P_BR_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST4B_Z_P_BR_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST4B_Z_P_BR_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


end ArmFull.Functions
