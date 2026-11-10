import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0150
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1059
import ArmFull.Fn.M1060

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

def decode_aarch32_instrs_SHA1C_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1C_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1H_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1H_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA1H_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1H_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA1M_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1M_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1M_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1M_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1P_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1P_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1P_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1P_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1SU0_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU0_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1SU0_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU0_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA1SU1_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU1_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA1SU1_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU1_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA256H_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA256H_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA256H2_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H2_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA256H2_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H2_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA256SU0_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU0_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA256SU0_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b10#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU0_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA256SU1_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU1_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_SHA256SU1_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveSHA256Ext ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU1_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVTA_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3804)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPToFixed w__2 0 is_unsigned w__3 rounding esize)) )
                : SailM (BitVec esize) )
              let w__5 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize (Sail.BitVec.castWidth w__4)))
                ) : SailM (BitVec 64) )
              (D_set (d +i r) w__5)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTA_vfp_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do
        (FPToFixed (Sail.BitVec.extractLsb w__0 15 0) 0 is_unsigned w__1 rounding 32) ) : SailM
        (BitVec 32) )
      (S_set d w__2))
  | 32 =>
    (do
      let w__3 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__5 ← (( do (FPToFixed w__3 0 is_unsigned w__4 rounding 32) ) : SailM (BitVec 32) )
      (S_set d w__5))
  | 64 =>
    (do
      let w__6 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__7 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__8 ← (( do (FPToFixed w__6 0 is_unsigned w__7 rounding 32) ) : SailM (BitVec 32) )
      (S_set d w__8))
  | _ => (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_exact : Bool, m : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRINTA_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (exact : Bool) (m : Nat) (regs : Nat) (rounding : FPRounding) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3819)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3820)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, result) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (op1, result)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, result) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                let w__3 ← (( do (FPRoundInt op1 w__2 rounding exact) ) : SailM (BitVec esize) )
                let result := (w__3 : (BitVec esize))
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure ((op1, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VRINTA_vfp_Op_A_txt (d : Nat) (esize : Nat) (exact : Bool) (m : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (FPRoundInt (Sail.BitVec.extractLsb w__0 15 0) w__1 rounding exact) ) :
        SailM (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ w__2)))
  | 32 =>
    (do
      let w__3 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__5 ← (( do (FPRoundInt w__3 w__4 rounding exact) ) : SailM (BitVec 32) )
      (S_set d w__5))
  | 64 =>
    (do
      let w__6 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__7 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__8 ← (( do (FPRoundInt w__6 w__7 rounding exact) ) : SailM (BitVec 64) )
      (D_set d w__8))
  | _ => (pure (()))


end ArmFull.Functions
