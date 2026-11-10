import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1210
import ArmFull.Fn.M1211
import ArmFull.Fn.M1212

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

def decode_LD3B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_LD3B_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD3B_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD3B_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD3B_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD3B_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD3H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_LD3H_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD3H_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD3H_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD3H_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD3H_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD3W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_LD3W_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD3W_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD3W_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD3W_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD3W_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD3D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_LD3D_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD3D_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD3D_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD3D_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD3D_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD4B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LD4B_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD4B_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD4B_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD4B_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD4B_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD4H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LD4H_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD4H_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD4H_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD4H_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD4H_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD4W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LD4W_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD4W_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD4W_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD4W_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD4W_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD4D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LD4D_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD4D_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD4D_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD4D_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD4D_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD2Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 128
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_LD2Q_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD2Q_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD2Q_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD2Q_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD2Q_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD3Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 128
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_LD3Q_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD3Q_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD3Q_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD3Q_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD3Q_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD4Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 128
  let offset : Int := (BitVec.toInt imm4)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LD4Q_Z_P_BI_Contiguous 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD4Q_Z_P_BI_Contiguous 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD4Q_Z_P_BI_Contiguous 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD4Q_Z_P_BI_Contiguous 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD4Q_Z_P_BI_Contiguous 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD1RQB_Z_P_BI_U8 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LD1RQB_Z_P_BI_U8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD1RQB_Z_P_BI_U8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD1RQB_Z_P_BI_U8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD1RQB_Z_P_BI_U8 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD1RQB_Z_P_BI_U8 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD1RQH_Z_P_BI_U16 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LD1RQH_Z_P_BI_U16 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD1RQH_Z_P_BI_U16 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD1RQH_Z_P_BI_U16 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD1RQH_Z_P_BI_U16 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD1RQH_Z_P_BI_U16 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD1RQW_Z_P_BI_U32 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LD1RQW_Z_P_BI_U32 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD1RQW_Z_P_BI_U32 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD1RQW_Z_P_BI_U32 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD1RQW_Z_P_BI_U32 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD1RQW_Z_P_BI_U32 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LD1RQD_Z_P_BI_U64 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LD1RQD_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD1RQD_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD1RQD_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD1RQD_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD1RQD_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


end ArmFull.Functions
