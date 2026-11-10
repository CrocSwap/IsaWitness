import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1245
import ArmFull.Fn.M1246
import ArmFull.Fn.M1247

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

def decode_LD1D_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let t : Int := (BitVec.toNat (Zt +++ 0b00#2))
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LD1D_MZ_P_BI_4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LD1D_MZ_P_BI_4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LD1D_MZ_P_BI_4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LD1D_MZ_P_BI_4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LD1D_MZ_P_BI_4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1B_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1B_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1B_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1B_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1B_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1B_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1H_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1H_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1H_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1H_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1H_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1H_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1W_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1W_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1W_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1W_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1W_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1W_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1D_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1D_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1D_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1D_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1D_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1D_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1B_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let t : Int := (BitVec.toNat (Zt +++ 0b00#2))
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1B_MZ_P_BI_4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1B_MZ_P_BI_4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1B_MZ_P_BI_4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1B_MZ_P_BI_4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1B_MZ_P_BI_4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1H_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let t : Int := (BitVec.toNat (Zt +++ 0b00#2))
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1H_MZ_P_BI_4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1H_MZ_P_BI_4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1H_MZ_P_BI_4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1H_MZ_P_BI_4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1H_MZ_P_BI_4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1W_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let t : Int := (BitVec.toNat (Zt +++ 0b00#2))
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1W_MZ_P_BI_4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1W_MZ_P_BI_4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1W_MZ_P_BI_4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1W_MZ_P_BI_4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1W_MZ_P_BI_4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_LDNT1D_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let t : Int := (BitVec.toNat (Zt +++ 0b00#2))
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNT1D_MZ_P_BI_4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_LDNT1D_MZ_P_BI_4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_LDNT1D_MZ_P_BI_4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_LDNT1D_MZ_P_BI_4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_LDNT1D_MZ_P_BI_4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST1B_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_ST1B_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST1B_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST1B_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST1B_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST1B_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST1H_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_ST1H_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST1H_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST1H_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST1H_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST1H_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST1W_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_ST1W_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST1W_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST1W_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST1W_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST1W_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST1D_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let t : Int := (BitVec.toNat (Zt +++ 0#1))
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_ST1D_MZ_P_BI_2 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST1D_MZ_P_BI_2 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST1D_MZ_P_BI_2 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST1D_MZ_P_BI_2 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST1D_MZ_P_BI_2 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_ST1B_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let t : Int := (BitVec.toNat (Zt +++ 0b00#2))
  let esize : Nat := 8
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_ST1B_MZ_P_BI_4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_ST1B_MZ_P_BI_4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_ST1B_MZ_P_BI_4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_ST1B_MZ_P_BI_4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_ST1B_MZ_P_BI_4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


end ArmFull.Functions
