import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0114
import ArmFull.Fn.M0117
import ArmFull.Fn.M0124
import ArmFull.Fn.M0228
import ArmFull.Fn.M1003
import ArmFull.Fn.M1013

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

def decode_aarch32_instrs_VSUBHN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vn 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSUBHN_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VSUBHN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vn 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSUBHN_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VSUB_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VSUB_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VSUBL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((op == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let is_vsubw : Bool := (op == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSUBL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) is_vsubw (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VSUBL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((op == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let is_vsubw : Bool := (op == 1#1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSUBL_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) is_vsubw (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VSWP_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSWP_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VSWP_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSWP_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VTBL_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (len : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let is_vtbl : Bool := (op == 0#1)
      let length : Int := ((BitVec.toNat len) +i 1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      if (((n +i length) >b 32) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VTBL_Op_A_txt (Sail.Int.toNatChecked (d)) is_vtbl
        (Sail.Int.toNatChecked (length)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VTBL_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (len : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let is_vtbl : Bool := (op == 0#1)
      let length : Int := ((BitVec.toNat len) +i 1)
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      if (((n +i length) >b 32) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VTBL_Op_A_txt (Sail.Int.toNatChecked (d)) is_vtbl
        (Sail.Int.toNatChecked (length)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VTRN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VTRN_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VTRN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VTRN_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VTST_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VTST_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VTST_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VTST_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VUZP_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let quadword_operation : Bool := (Q == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VUZP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) quadword_operation))
  else (pure (()))


def decode_aarch32_instrs_VUZP_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let quadword_operation : Bool := (Q == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VUZP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) quadword_operation))
  else (pure (()))


def decode_aarch32_instrs_VZIP_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let quadword_operation : Bool := (Q == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VZIP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) quadword_operation))
  else (pure (()))


def decode_aarch32_instrs_VZIP_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let quadword_operation : Bool := (Q == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VZIP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) quadword_operation))
  else (pure (()))


def decode_aarch32_instrs_VMRS_A1enc_AS_txt (cond : (BitVec 4)) (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:41998.29-41998.30"
      let t : Int := (BitVec.toNat Rt)
      if ((let b__0 := reg
         (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
           then true
           else
             (match b__0 with
             | 0b0101 => true
             | b__0 =>
               (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
               then true
               else
                 (match b__0 with
                 | 0b1000 => true
                 | _ => false))) : Bool))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((t == 15) && (reg != 0b0001#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMRS_Op_AS_txt reg (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_VMRS_T1enc_AS_txt (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      if ((let b__0 := reg
         (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
           then true
           else
             (match b__0 with
             | 0b0101 => true
             | b__0 =>
               (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
               then true
               else
                 (match b__0 with
                 | 0b1000 => true
                 | _ => false))) : Bool))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((t == 15) && (reg != 0b0001#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMRS_Op_AS_txt reg (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_VMSR_A1enc_AS_txt (cond : (BitVec 4)) (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:42089.29-42089.30"
      let t : Int := (BitVec.toNat Rt)
      if (((let b__0 := reg
           (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
             then true
             else false : Bool))) && (reg != 0b1000#4)) : Bool)
      then
        (do
          let c ← (( do (ConstrainUnpredictable Unpredictable_VMSR) ) : SailM Constraint )
          ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs32.sail:42096.62-42096.63"
          match c with
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ()))
          | _ => (pure (())))
      else (pure (()))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMSR_Op_AS_txt reg (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_VMSR_T1enc_AS_txt (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      if (((let b__0 := reg
           (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
             then true
             else false : Bool))) && (reg != 0b1000#4)) : Bool)
      then
        (do
          let c ← (( do (ConstrainUnpredictable Unpredictable_VMSR) ) : SailM Constraint )
          ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs32.sail:42137.62-42137.63"
          match c with
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ()))
          | _ => (pure (())))
      else (pure (()))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMSR_Op_AS_txt reg (Sail.Int.toNatChecked (t))))
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESD_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let op1 ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (AESInvSubBytes (AESInvShiftRows (op1 ^^^ op2))) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__0)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESE_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let op1 ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (AESSubBytes (AESShiftRows (op1 ^^^ op2))) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__0)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESIMC_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let w__0 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let w__1 ← (( do (AESInvMixColumns w__0) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__1)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESMC_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let w__0 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let w__1 ← (( do (AESMixColumns w__0) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__1)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1C_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let t ← (( do (undefined_bitvector_at (← occLabel 3797) 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let x ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let y : (BitVec 32) := (Sail.BitVec.extractLsb w__0 31 0)
  let w ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let (t, x, y) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (t, x, y)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (t, x, y) := loop_vars
        loop_vars ← do
          let t : (BitVec 32) :=
            (SHAchoose (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64)
              (Sail.BitVec.extractLsb x 127 96))
          let w__1 ← (( do (ROL (Sail.BitVec.extractLsb x 31 0) 5) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let y := ((((y + w__1) + t) + w__2) : (BitVec 32))
          let w__3 ← (( do (ROL (Sail.BitVec.extractLsb x 63 32) 30) ) : SailM (BitVec 32) )
          let x := ((Sail.BitVec.updateSubrange x 63 32 w__3) : (BitVec 128))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (32 + 128)) )
          let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((t, x, y)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (Q_set (Int.shiftl d 1) x)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1H_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let w__0 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb w__0 31 0) 30) ) : SailM (BitVec 32) )
  (Q_set (Int.shiftl d 1) (Sail.BitVec.zeroExtend w__1 128))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1M_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let t ← (( do (undefined_bitvector_at (← occLabel 3798) 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let x ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let y : (BitVec 32) := (Sail.BitVec.extractLsb w__0 31 0)
  let w ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let (t, x, y) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (t, x, y)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (t, x, y) := loop_vars
        loop_vars ← do
          let t : (BitVec 32) :=
            (SHAmajority (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64)
              (Sail.BitVec.extractLsb x 127 96))
          let w__1 ← (( do (ROL (Sail.BitVec.extractLsb x 31 0) 5) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let y := ((((y + w__1) + t) + w__2) : (BitVec 32))
          let w__3 ← (( do (ROL (Sail.BitVec.extractLsb x 63 32) 30) ) : SailM (BitVec 32) )
          let x := ((Sail.BitVec.updateSubrange x 63 32 w__3) : (BitVec 128))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (32 + 128)) )
          let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((t, x, y)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (Q_set (Int.shiftl d 1) x)


end ArmFull.Functions
