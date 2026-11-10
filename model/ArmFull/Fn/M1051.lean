import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0015
import ArmFull.Fn.M0099
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0167
import ArmFull.Fn.M0175
import ArmFull.Fn.M1009

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

def decode_aarch32_instrs_VMOV_r_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:28974.29-28974.30"
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let single_register : Bool := (size == 0b10#2)
      let advsimd : Bool := false
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3509) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3510) 0 31))) ) :
        SailM Nat )
      let regs : Int := 1
      let (d, m, regs) : (Nat × Nat × Int) :=
        if (single_register : Bool)
        then
          (let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, m, regs))
        else
          (let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          let regs : Int := 1
          (d, m, regs))
      let regs : Int := regs
      let m : Int := m
      let d : Int := d
      (execute_aarch32_instrs_VMOV_r_Op_A_txt advsimd (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_r_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let single_register : Bool := (size == 0b10#2)
      let advsimd : Bool := false
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3511) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3512) 0 31))) ) :
        SailM Nat )
      let regs : Int := 1
      let (d, m, regs) : (Nat × Nat × Int) :=
        if (single_register : Bool)
        then
          (let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, m, regs))
        else
          (let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          let regs : Int := 1
          (d, m, regs))
      let regs : Int := regs
      let m : Int := m
      let d : Int := d
      (execute_aarch32_instrs_VMOV_r_Op_A_txt advsimd (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) single_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_rs_A1enc_A_txt (cond : (BitVec 4)) (opc1 : (BitVec 2)) (Vd : (BitVec 4)) (Rt : (BitVec 4)) (D : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29062.29-29062.30"
      let advsimd ← (( do (undefined_bool_at (← occLabel 3513) ()) ) : SailM Bool )
      let esize : Int := 8
      let index ← (( do (undefined_int_at (← occLabel 3514) ()) ) : SailM Int )
      let b__0 := (opc1 +++ opc2)
      let (advsimd, esize, index) ← (( do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (1#1 : (BitVec 1))) : Bool)
        then
          (let advsimd : Bool := true
          let esize : Int := 8
          let index : Int :=
            (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ opc2))
          (pure ((advsimd, esize, index))))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
            then
              (let advsimd : Bool := true
              let esize : Int := 16
              let index : Int :=
                (BitVec.toNat
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        opc2 1)]))))
              (pure ((advsimd, esize, index))))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                then
                  (let advsimd : Bool := false
                  let esize : Int := 32
                  let index : Int :=
                    (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])))
                  (pure ((advsimd, esize, index))))
                else sailThrow ((Error_Undefined ())))) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index : Int := index
      let esize : Int := esize
      let d : Int := (BitVec.toNat (D +++ Vd))
      let t : Int := (BitVec.toNat Rt)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) 8 index
            (Sail.Int.toNatChecked (t))))
      | 16 =>
        (do
          (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) 16 index
            (Sail.Int.toNatChecked (t))))
      | 32 =>
        (do
          (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) 32 index
            (Sail.Int.toNatChecked (t))))
      | _ =>
        (do
          ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29105.26-29105.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VMOV_rs_T1enc_A_txt (opc1 : (BitVec 2)) (Vd : (BitVec 4)) (Rt : (BitVec 4)) (D : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let advsimd ← (( do (undefined_bool_at (← occLabel 3515) ()) ) : SailM Bool )
      let esize : Int := 8
      let index ← (( do (undefined_int_at (← occLabel 3516) ()) ) : SailM Int )
      let b__0 := (opc1 +++ opc2)
      let (advsimd, esize, index) ← (( do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (1#1 : (BitVec 1))) : Bool)
        then
          (let advsimd : Bool := true
          let esize : Int := 8
          let index : Int :=
            (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ opc2))
          (pure ((advsimd, esize, index))))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
            then
              (let advsimd : Bool := true
              let esize : Int := 16
              let index : Int :=
                (BitVec.toNat
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        opc2 1)]))))
              (pure ((advsimd, esize, index))))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                then
                  (let advsimd : Bool := false
                  let esize : Int := 32
                  let index : Int :=
                    (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])))
                  (pure ((advsimd, esize, index))))
                else sailThrow ((Error_Undefined ())))) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index : Int := index
      let esize : Int := esize
      let d : Int := (BitVec.toNat (D +++ Vd))
      let t : Int := (BitVec.toNat Rt)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) 8 index
            (Sail.Int.toNatChecked (t))))
      | 16 =>
        (do
          (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) 16 index
            (Sail.Int.toNatChecked (t))))
      | 32 =>
        (do
          (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) 32 index
            (Sail.Int.toNatChecked (t))))
      | _ =>
        (do
          ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29173.26-29173.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VMOV_s_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29211.29-29211.30"
      let to_arm_register : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_s_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) to_arm_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_s_T1enc_A_txt (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let to_arm_register : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_s_Op_A_txt (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) to_arm_register))
  else (pure (()))


def decode_aarch32_instrs_VMOV_sr_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (opc1 : (BitVec 2)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29282.29-29282.30"
      let advsimd ← (( do (undefined_bool_at (← occLabel 3517) ()) ) : SailM Bool )
      let esize : Int := 8
      let index ← (( do (undefined_int_at (← occLabel 3518) ()) ) : SailM Int )
      let b__0 := ((U +++ opc1) +++ opc2)
      let (advsimd, esize, index) ← (( do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (1#1 : (BitVec 1))) : Bool)
        then
          (let advsimd : Bool := true
          let esize : Int := 8
          let index : Int :=
            (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ opc2))
          (pure ((advsimd, esize, index))))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
            then
              (let advsimd : Bool := true
              let esize : Int := 16
              let index : Int :=
                (BitVec.toNat
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        opc2 1)]))))
              (pure ((advsimd, esize, index))))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                then
                  (let advsimd : Bool := false
                  let esize : Int := 32
                  let index : Int :=
                    (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])))
                  (pure ((advsimd, esize, index))))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then sailThrow ((Error_Undefined ()))
                    else sailThrow ((Error_Undefined ()))
                    (pure ((advsimd, esize, index)))))) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index : Int := index
      let esize : Int := esize
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat (N +++ Vn))
      let is_unsigned : Bool := (U == 1#1)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 8 index (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (t)) is_unsigned))
      | 16 =>
        (do
          (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 16 index (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (t)) is_unsigned))
      | 32 =>
        (do
          (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 32 index (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ =>
        (do
          ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29329.26-29329.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VMOV_sr_T1enc_A_txt (U : (BitVec 1)) (opc1 : (BitVec 2)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let advsimd ← (( do (undefined_bool_at (← occLabel 3519) ()) ) : SailM Bool )
      let esize : Int := 8
      let index ← (( do (undefined_int_at (← occLabel 3520) ()) ) : SailM Int )
      let b__0 := ((U +++ opc1) +++ opc2)
      let (advsimd, esize, index) ← (( do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (1#1 : (BitVec 1))) : Bool)
        then
          (let advsimd : Bool := true
          let esize : Int := 8
          let index : Int :=
            (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ opc2))
          (pure ((advsimd, esize, index))))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
            then
              (let advsimd : Bool := true
              let esize : Int := 16
              let index : Int :=
                (BitVec.toNat
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        opc2 1)]))))
              (pure ((advsimd, esize, index))))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                then
                  (let advsimd : Bool := false
                  let esize : Int := 32
                  let index : Int :=
                    (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 0)])))
                  (pure ((advsimd, esize, index))))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then sailThrow ((Error_Undefined ()))
                    else sailThrow ((Error_Undefined ()))
                    (pure ((advsimd, esize, index)))))) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index : Int := index
      let esize : Int := esize
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat (N +++ Vn))
      let is_unsigned : Bool := (U == 1#1)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      match esize with
      | 8 =>
        (do
          (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 8 index (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (t)) is_unsigned))
      | 16 =>
        (do
          (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 16 index (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (t)) is_unsigned))
      | 32 =>
        (do
          (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 32 index (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ =>
        (do
          ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29402.26-29402.27"
          throw Error.Exit))
  else (pure (()))


def decode_aarch32_instrs_VMOV_ss_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:29443.29-29443.30"
      let to_arm_registers : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let m : Int := (BitVec.toNat (Vm +++ M))
      if ((((t == 15) || (t2 == 15)) || (m == 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((to_arm_registers && (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_ss_Op_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) to_arm_registers))
  else (pure (()))


def decode_aarch32_instrs_VMOV_ss_T1enc_A_txt (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let to_arm_registers : Bool := (op == 1#1)
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let m : Int := (BitVec.toNat (Vm +++ M))
      if ((((t == 15) || (t2 == 15)) || (m == 31)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((to_arm_registers && (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_VMOV_ss_Op_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) to_arm_registers))
  else (pure (()))


def decode_aarch32_instrs_VMUL_i_A1enc_A_txt (op : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) || ((op == 1#1) && (size != 0b00#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := false
      let polynomial : Bool := (op == 1#1)
      let long_destination : Bool := false
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMUL_i_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) polynomial (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMUL_i_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let polynomial : Bool := (op == 1#1)
      let long_destination : Bool := true
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let (elements, esize) ← (( do
        if (polynomial : Bool)
        then
          (do
            if (((U == 1#1) || (size == 0b01#2)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            if ((size == 0b10#2) : Bool)
            then
              (do
                let w__1 ← (( do (HaveBit128PMULLExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (()))
                let esize : Int := 64
                let elements : Int := 1
                (pure ((elements, esize))))
            else (pure ((elements, esize))))
        else (pure ((elements, esize))) ) : SailM (Int × Int) )
      let esize : Int := esize
      let elements : Int := elements
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Nat := 1
      (execute_aarch32_instrs_VMUL_i_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) polynomial regs is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMUL_i_T1enc_A_txt (op : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((size == 0b11#2) || ((op == 1#1) && (size != 0b00#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let is_unsigned : Bool := false
      let polynomial : Bool := (op == 1#1)
      let long_destination : Bool := false
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMUL_i_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) polynomial (Sail.Int.toNatChecked (regs)) is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMUL_i_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let is_unsigned : Bool := (U == 1#1)
      let polynomial : Bool := (op == 1#1)
      let long_destination : Bool := true
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let (elements, esize) ← (( do
        if (polynomial : Bool)
        then
          (do
            if (((U == 1#1) || (size == 0b01#2)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            if ((size == 0b10#2) : Bool)
            then
              (do
                let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
                if (w__1 : Bool)
                then sailThrow ((Error_Unpredictable ()))
                else (pure (()))
                let w__2 ← (( do (HaveBit128PMULLExt ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (()))
                let esize : Int := 64
                let elements : Int := 1
                (pure ((elements, esize))))
            else (pure ((elements, esize))))
        else (pure ((elements, esize))) ) : SailM (Int × Int) )
      let esize : Int := esize
      let elements : Int := elements
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Nat := 1
      (execute_aarch32_instrs_VMUL_i_Op_A_txt (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) long_destination (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) polynomial regs is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VMVN_i_A1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 cmode 3 2)) != 0b11#2)) || ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               cmode 3 1)) == 0b111#3)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let imm64 ← (( do (AdvSIMDExpandImm 1#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64)
        )
      let d : Int := (BitVec.toNat (D +++ Vd))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMVN_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm64
        (Sail.Int.toNatChecked (regs))))
  else (pure (()))


end ArmFull.Functions
