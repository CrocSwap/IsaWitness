import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0019
import ArmFull.Fn.M0040
import ArmFull.Fn.M0117
import ArmFull.Fn.M0118
import ArmFull.Fn.M0120
import ArmFull.Fn.M0121
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0198
import ArmFull.Fn.M0241
import ArmFull.Fn.M0580
import ArmFull.Fn.M1174
import ArmFull.Fn.M1182

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

def decode_aarch32_instrs_LDAB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:42864.29-42864.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAB_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAB_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAEX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:42927.29-42927.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEX_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAEX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEX_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAEXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:42990.29-42990.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEXB_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAEXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEXB_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAEXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:43057.29-43057.30"
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) || (t2 == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEXD_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_LDAEXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let n : Int := (BitVec.toNat Rn)
      if (((((t == 15) || (t2 == 15)) || (t == t2)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEXD_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_LDAEXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:43123.29-43123.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEXH_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAEXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAEXH_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:43185.29-43185.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAH_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDAH_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STL_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44146.29-44146.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STL_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STL_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STL_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44208.29-44208.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLB_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLB_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLEX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44275.29-44275.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLEX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEX_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLEXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44352.29-44352.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEXB_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLEXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEXB_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLEXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44433.29-44433.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      if (((((d == 15) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1)) || (t2 == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((d == n) || (d == t)) || (d == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEXD_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_STLEXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let n : Int := (BitVec.toNat Rn)
      if (((((d == 15) || (t == 15)) || (t2 == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((d == n) || (d == t)) || (d == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEXD_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_STLEXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44509.29-44509.30"
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEXH_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLEXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((d == n) || (d == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLEXH_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:44581.29-44581.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLH_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_STLH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STLH_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp := ReduceOp_ADD
  (execute_aarch64_instrs_vector_reduce_add_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let op : ReduceOp := ReduceOp_ADD
  (execute_aarch64_instrs_vector_reduce_add_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def execute_aarch64_instrs_branch_unconditional_immediate (branch_type : BranchType) (offset : (BitVec 64)) : SailM Unit := do
  if ((BEq.beq branch_type BranchType_DIRCALL) : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             (HaveGCS ())) : Bool)
        then
          (do
            let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
            (GCSPCREnabled w__1.EL))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
          (AddGCSRecord (BitVec.addInt w__4 4)))
      else (pure (()))
      let w__5 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (X_set 30 64 (BitVec.addInt w__5 4)))
  else (pure (()))
  let branch_conditional : Bool := false
  let w__6 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  (BranchTo (w__6 + offset) branch_type branch_conditional)


/-- Type quantifiers: m : Nat, n : Nat, k_pac : Bool, k_source_is_sp : Bool, k_use_key_a : Bool, 0
  ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch64_instrs_branch_unconditional_register (branch_type : BranchType) (m : Nat) (n : Nat) (pac : Bool) (source_is_sp : Bool) (use_key_a : Bool) : SailM Unit := do
  let inst_type ← (( do (undefined_GCSInstruction (← occLabel 4004) ()) ) : SailM GCSInstruction
    )
  let target ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let auth_then_branch : Bool := true
  let target ← (( do
    if (pac : Bool)
    then
      (do
        let modifier ← (( do
          if (source_is_sp : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read m 64)) ) : SailM (BitVec 64) )
        if (use_key_a : Bool)
        then
          (do
            (AuthIA target modifier auth_then_branch))
        else
          (do
            (AuthIB target modifier auth_then_branch)))
    else (pure (target)) ) : SailM (BitVec 64) )
  let w__8 ← (( do
    if ((← do
         if (((BEq.beq branch_type BranchType_RET) : Bool) : Bool)
         then
           (do
             (HaveGCS ()))
         else (pure false)) : Bool)
    then
      (do
        let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
        (GCSPCREnabled w__6.EL))
    else (pure false) ) : SailM Bool )
  let target ← (( do
    if (w__8 : Bool)
    then
      (do
        let inst_type : GCSInstruction :=
          if ((! pac) : Bool)
          then GCSInstType_PRET
          else
            (if (use_key_a : Bool)
            then GCSInstType_PRETAA
            else GCSInstType_PRETAB)
        let w__9 ← (( do (LoadCheckGCSRecord target inst_type) ) : SailM (BitVec 64) )
        let target := (w__9 : (BitVec 64))
        let w__10 ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
        (SetCurrentGCSPointer (BitVec.addInt w__10 8))
        (pure (target)))
    else (pure (target)) ) : SailM (BitVec 64) )
  if ((BEq.beq branch_type BranchType_INDCALL) : Bool)
  then
    (do
      let w__14 ← (( do
        if ((← do
             (HaveGCS ())) : Bool)
        then
          (do
            let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
            (GCSPCREnabled w__12.EL))
        else (pure false) ) : SailM Bool )
      if (w__14 : Bool)
      then
        (do
          let w__15 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
          (AddGCSRecord (BitVec.addInt w__15 4)))
      else (pure (()))
      let w__16 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (X_set 30 64 (BitVec.addInt w__16 4)))
  else (pure (()))
  match branch_type with
  | .BranchType_INDIR =>
    (do
      let w__17 ← (( do readReg InGuardedPage ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          if (((n == 16) || (n == 17)) : Bool)
          then
            (do
              writeReg BTypeNext 0b01#2)
          else
            (do
              writeReg BTypeNext 0b11#2))
      else
        (do
          writeReg BTypeNext 0b01#2))
  | .BranchType_INDCALL =>
    (do
      writeReg BTypeNext 0b10#2)
  | .BranchType_RET =>
    (do
      writeReg BTypeNext 0b00#2)
  | _ => (pure (()))
  let branch_conditional : Bool := false
  (BranchTo target branch_type branch_conditional)


def decode_cpyp_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4060) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8037.58-8037.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


end ArmFull.Functions
