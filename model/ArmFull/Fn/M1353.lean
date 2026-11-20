module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M1242
public import ArmFull.Fn.M1243 set_option backward.proofsInPublic true @[expose] public section

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

def decode_aarch32_instrs_VSTR_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:39367.29-39367.30"
      let w__3 ← (( do
        if (((size == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((size == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let add : Bool := (U == 1#1)
      let imm32 : (BitVec 32) :=
        if ((esize == 16) : Bool)
        then (Sail.BitVec.zeroExtend (imm8 +++ 0#1) 32)
        else (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3754) 0 31))) ) :
        SailM Nat )
      let d : Nat :=
        match size with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d : Int := d
      let n : Int := (BitVec.toNat Rn)
      let w__5 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          (do
            let w__4 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
            (pure (((bne w__4 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d : Int := d
      (execute_aarch32_instrs_VSTR_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_VSTR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__3 ← (( do
        if (((size == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((size == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__5 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let add : Bool := (U == 1#1)
      let imm32 : (BitVec 32) :=
        if ((esize == 16) : Bool)
        then (Sail.BitVec.zeroExtend (imm8 +++ 0#1) 32)
        else (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3755) 0 31))) ) :
        SailM Nat )
      let d : Nat :=
        match size with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d : Int := d
      let n : Int := (BitVec.toNat Rn)
      let w__7 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          (do
            let w__6 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
            (pure (((bne w__6 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__7 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d : Int := d
      (execute_aarch32_instrs_VSTR_Op_A_txt add (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_LDM_e_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 15)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:40995.29-40995.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 15) := register_list
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_e_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) registers
        wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_LDM_u_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 15)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:41055.29-41055.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 15) := register_list
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_u_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) registers
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_RFE_A1enc_AS_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) wback
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_RFE_T1enc_AS_txt (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := false
      let wordhigher : Bool := false
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) wback
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_RFE_T2enc_AS_txt (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := true
      let wordhigher : Bool := false
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) wback
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_SRS_A1enc_AS_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      (execute_aarch32_instrs_SRS_OpA_AS_txt increment_name mode wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_SRS_T1enc_AS_txt (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := false
      let wordhigher : Bool := false
      (execute_aarch32_instrs_SRS_OpT_AS_txt increment_name mode wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_SRS_T2enc_AS_txt (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := true
      let wordhigher : Bool := false
      (execute_aarch32_instrs_SRS_OpT_AS_txt increment_name mode wback wordhigher))
  else (pure (()))


def decode_aarch32_instrs_STM_u_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:41928.29-41928.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STM_u_Op_AS_txt increment_name (Sail.Int.toNatChecked (n)) registers
        wordhigher))
  else (pure (()))


def decode_aarch32_instrs_LDA_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:42802.29-42802.30"
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDA_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDA_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDA_Op_A_txt (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDAB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:42864.29-42864.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:42927.29-42927.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:42990.29-42990.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:43057.29-43057.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:43123.29-43123.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:43185.29-43185.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:44146.29-44146.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:44208.29-44208.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:44275.29-44275.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:44352.29-44352.30"
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
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:44433.29-44433.30"
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


end ArmFull.Functions
