import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1249
import ArmFull.Fn.M1250
import ArmFull.Fn.M1251

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

def decode_LD1Q_ZA_P_RRR__ (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (0#1 +++ Pg))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let t : Int := (BitVec.toNat ZAt)
  let offset : Nat := 0
  let esize : Nat := 128
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_LD1Q_ZA_P_RRR__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 256 =>
    (do
      (execute_LD1Q_ZA_P_RRR__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 512 =>
    (do
      (execute_LD1Q_ZA_P_RRR__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 1024 =>
    (do
      (execute_LD1Q_ZA_P_RRR__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 2048 =>
    (do
      (execute_LD1Q_ZA_P_RRR__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | _ => (pure (()))


def decode_ST1B_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (0#1 +++ Pg))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let t : Nat := 0
  let offset : Int := (BitVec.toNat off4)
  let esize : Nat := 8
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_ST1B_ZA_P_RRR__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) t
        vertical))
  | 256 =>
    (do
      (execute_ST1B_ZA_P_RRR__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) t
        vertical))
  | 512 =>
    (do
      (execute_ST1B_ZA_P_RRR__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) t
        vertical))
  | 1024 =>
    (do
      (execute_ST1B_ZA_P_RRR__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) t
        vertical))
  | 2048 =>
    (do
      (execute_ST1B_ZA_P_RRR__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) t
        vertical))
  | _ => (pure (()))


def decode_ST1H_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (0#1 +++ Pg))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let t : Int := (BitVec.toNat ZAt)
  let offset : Int := (BitVec.toNat off3)
  let esize : Nat := 16
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_ST1H_ZA_P_RRR__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 256 =>
    (do
      (execute_ST1H_ZA_P_RRR__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 512 =>
    (do
      (execute_ST1H_ZA_P_RRR__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 1024 =>
    (do
      (execute_ST1H_ZA_P_RRR__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 2048 =>
    (do
      (execute_ST1H_ZA_P_RRR__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | _ => (pure (()))


def decode_ST1W_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (0#1 +++ Pg))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let t : Int := (BitVec.toNat ZAt)
  let offset : Int := (BitVec.toNat off2)
  let esize : Nat := 32
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_ST1W_ZA_P_RRR__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 256 =>
    (do
      (execute_ST1W_ZA_P_RRR__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 512 =>
    (do
      (execute_ST1W_ZA_P_RRR__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 1024 =>
    (do
      (execute_ST1W_ZA_P_RRR__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 2048 =>
    (do
      (execute_ST1W_ZA_P_RRR__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | _ => (pure (()))


def decode_ST1D_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 3)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (0#1 +++ Pg))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let t : Int := (BitVec.toNat ZAt)
  let offset : Int := (BitVec.toNat o1)
  let esize : Nat := 64
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_ST1D_ZA_P_RRR__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 256 =>
    (do
      (execute_ST1D_ZA_P_RRR__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 512 =>
    (do
      (execute_ST1D_ZA_P_RRR__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 1024 =>
    (do
      (execute_ST1D_ZA_P_RRR__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | 2048 =>
    (do
      (execute_ST1D_ZA_P_RRR__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) vertical))
  | _ => (pure (()))


def decode_ST1Q_ZA_P_RRR__ (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (0#1 +++ Pg))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let t : Int := (BitVec.toNat ZAt)
  let offset : Nat := 0
  let esize : Nat := 128
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_ST1Q_ZA_P_RRR__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 256 =>
    (do
      (execute_ST1Q_ZA_P_RRR__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 512 =>
    (do
      (execute_ST1Q_ZA_P_RRR__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 1024 =>
    (do
      (execute_ST1Q_ZA_P_RRR__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | 2048 =>
    (do
      (execute_ST1Q_ZA_P_RRR__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
        vertical))
  | _ => (pure (()))


def decode_LD1B_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let tstride : Nat := 8
  let t : Int := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_LD1B_MZx_P_BR_2x8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1B_MZx_P_BR_2x8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1B_MZx_P_BR_2x8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1B_MZx_P_BR_2x8 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1B_MZx_P_BR_2x8 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1H_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let tstride : Nat := 8
  let t : Int := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_LD1H_MZx_P_BR_2x8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1H_MZx_P_BR_2x8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1H_MZx_P_BR_2x8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1H_MZx_P_BR_2x8 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1H_MZx_P_BR_2x8 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1W_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let tstride : Nat := 8
  let t : Int := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_LD1W_MZx_P_BR_2x8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1W_MZx_P_BR_2x8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1W_MZx_P_BR_2x8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1W_MZx_P_BR_2x8 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1W_MZx_P_BR_2x8 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1D_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let tstride : Nat := 8
  let t : Int := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_LD1D_MZx_P_BR_2x8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1D_MZx_P_BR_2x8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1D_MZx_P_BR_2x8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1D_MZx_P_BR_2x8 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1D_MZx_P_BR_2x8 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1B_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_LD1B_MZx_P_BR_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1B_MZx_P_BR_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1B_MZx_P_BR_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1B_MZx_P_BR_4x4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1B_MZx_P_BR_4x4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1H_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_LD1H_MZx_P_BR_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1H_MZx_P_BR_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1H_MZx_P_BR_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1H_MZx_P_BR_4x4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1H_MZx_P_BR_4x4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1W_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_LD1W_MZx_P_BR_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1W_MZx_P_BR_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1W_MZx_P_BR_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1W_MZx_P_BR_4x4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1W_MZx_P_BR_4x4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LD1D_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_LD1D_MZx_P_BR_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LD1D_MZx_P_BR_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LD1D_MZx_P_BR_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LD1D_MZx_P_BR_4x4 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_LD1D_MZx_P_BR_4x4 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_LDNT1B_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let tstride : Nat := 8
  let t : Int := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_LDNT1B_MZx_P_BR_2x8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LDNT1B_MZx_P_BR_2x8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LDNT1B_MZx_P_BR_2x8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LDNT1B_MZx_P_BR_2x8 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))
        tstride))
  | 2048 =>
    (do
      (execute_LDNT1B_MZx_P_BR_2x8 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))
        tstride))
  | _ => (pure (()))


def decode_LDNT1H_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  let tstride : Nat := 8
  let t : Int := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_LDNT1H_MZx_P_BR_2x8 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_LDNT1H_MZx_P_BR_2x8 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_LDNT1H_MZx_P_BR_2x8 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_LDNT1H_MZx_P_BR_2x8 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))
        tstride))
  | 2048 =>
    (do
      (execute_LDNT1H_MZx_P_BR_2x8 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (t))
        tstride))
  | _ => (pure (()))


end ArmFull.Functions
