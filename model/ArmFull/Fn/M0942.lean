import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M0859
import ArmFull.Fn.M0860

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

def decode_CMPHI_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let imm : Int := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPHI_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPHI_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPHI_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPHI_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPHI_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPLO_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let imm : Int := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPLO_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPLO_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPLO_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPLO_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPLO_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPLS_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let imm : Int := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPLS_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPLS_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPLS_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPLS_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPLS_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPGE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let imm : Int := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CMPGE_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 256 =>
    (do
      (execute_CMPGE_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 512 =>
    (do
      (execute_CMPGE_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 1024 =>
    (do
      (execute_CMPGE_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 2048 =>
    (do
      (execute_CMPGE_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | _ => (pure (()))


def decode_CMPGT_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let imm : Int := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CMPGT_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 256 =>
    (do
      (execute_CMPGT_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 512 =>
    (do
      (execute_CMPGT_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 1024 =>
    (do
      (execute_CMPGT_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 2048 =>
    (do
      (execute_CMPGT_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | _ => (pure (()))


def decode_CMPLT_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let imm : Int := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CMPLT_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 256 =>
    (do
      (execute_CMPLT_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 512 =>
    (do
      (execute_CMPLT_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 1024 =>
    (do
      (execute_CMPLT_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 2048 =>
    (do
      (execute_CMPLT_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | _ => (pure (()))


def decode_CMPLE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let imm : Int := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CMPLE_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 256 =>
    (do
      (execute_CMPLE_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 512 =>
    (do
      (execute_CMPLE_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 1024 =>
    (do
      (execute_CMPLE_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | 2048 =>
    (do
      (execute_CMPLE_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
  | _ => (pure (()))


def decode_CMPEQ_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_EQ
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CMPEQ_P_P_ZW__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPEQ_P_P_ZW__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPEQ_P_P_ZW__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPEQ_P_P_ZW__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPEQ_P_P_ZW__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPNE_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_NE
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CMPNE_P_P_ZW__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPNE_P_P_ZW__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPNE_P_P_ZW__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPNE_P_P_ZW__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPNE_P_P_ZW__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPHS_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPHS_P_P_ZW__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPHS_P_P_ZW__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPHS_P_P_ZW__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPHS_P_P_ZW__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPHS_P_P_ZW__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPHI_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPHI_P_P_ZW__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPHI_P_P_ZW__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPHI_P_P_ZW__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPHI_P_P_ZW__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPHI_P_P_ZW__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPLO_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPLO_P_P_ZW__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPLO_P_P_ZW__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPLO_P_P_ZW__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPLO_P_P_ZW__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPLO_P_P_ZW__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


def decode_CMPLS_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CMPLS_P_P_ZW__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 256 =>
    (do
      (execute_CMPLS_P_P_ZW__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 512 =>
    (do
      (execute_CMPLS_P_P_ZW__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 1024 =>
    (do
      (execute_CMPLS_P_P_ZW__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | 2048 =>
    (do
      (execute_CMPLS_P_P_ZW__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
        is_unsigned))
  | _ => (pure (()))


end ArmFull.Functions
