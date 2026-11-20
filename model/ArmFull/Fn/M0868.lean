module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0164
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0235
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0606
public import ArmFull.Fn.M0862
public import ArmFull.Fn.M0865 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysInstr128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (AArch64_AutoGen_SysOpsWrite128 w__0.EL (integer_subrange op0 1 0) (integer_subrange op1 2 0)
    (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t t2)


def decode_aarch32_instrs_SVC_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:16058.29-16058.30"
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm24 32)
      (execute_aarch32_instrs_SVC_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_SVC_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_SVC_Op_A_txt imm32))
  else (pure (()))


def execute_aarch32_instrs_WFE_Op_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (IsEventRegisterSet ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (ClearEventRegister ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL0) : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL1 WFxType_WFE))
      else (pure (()))
      let w__8 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__2.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__3.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__7) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL2 WFxType_WFE))
      else (pure (()))
      let w__11 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__10.M != M32_Monitor) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL3 WFxType_WFE))
      else (pure (()))
      let localtimeout : Int := (Int.shiftl 1 64)
      (WaitForEvent localtimeout))


def execute_aarch32_instrs_WFI_Op_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (InterruptPending ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL0) : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL1 WFxType_WFI))
      else (pure (()))
      let w__8 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__2.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__3.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__7) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL2 WFxType_WFI))
      else (pure (()))
      let w__11 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__10.M != M32_Monitor) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL3 WFxType_WFI))
      else (pure (()))
      let localtimeout : Int := (Int.shiftl 1 64)
      (WaitForInterrupt localtimeout))
  else (pure (()))


def decode_aarch32_instrs_HVC_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:40919.25-40919.26"
  if ((cond != 0b1110#4) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let imm16 : (BitVec 16) := (imm12 +++ imm4)
  (execute_aarch32_instrs_HVC_Op_AS_txt imm16)


def decode_aarch32_instrs_HVC_T1enc_A_txt (imm4 : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let imm16 : (BitVec 16) := (imm4 +++ imm12)
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_HVC_Op_AS_txt imm16)


def decode_aarch32_instrs_SMC_A1enc_AS_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:41716.29-41716.30"
      (execute_aarch32_instrs_SMC_Op_AS_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SMC_T1enc_AS_txt (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
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
      (execute_aarch32_instrs_SMC_Op_AS_txt ()))
  else (pure (()))


def decode_abs_aarch64_instrs_integer_arithmetic_unary_abs (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let d : Int := (BitVec.toNat Rd)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_unary_abs (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n))))


def decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  if ((shift == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
          let shift_amount : Int := (BitVec.toNat imm6)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift_amount)) shift_type
            sub_op)))


def decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  if ((shift == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
          let shift_amount : Int := (BitVec.toNat imm6)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift_amount)) shift_type
            sub_op)))


def decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  if ((shift == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
          let shift_amount : Int := (BitVec.toNat imm6)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift_amount)) shift_type
            sub_op)))


def decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  if ((shift == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
          let shift_amount : Int := (BitVec.toNat imm6)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift_amount)) shift_type
            sub_op)))


def decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3924)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    match sh with
    | 0 => (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked (datasize))))
    | _ =>
      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (imm12 +++ (Zeros (n := 12)))
        (Sail.Int.toNatChecked (datasize))))
  let imm := imm
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3925)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    match sh with
    | 0 => (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked (datasize))))
    | _ =>
      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (imm12 +++ (Zeros (n := 12)))
        (Sail.Int.toNatChecked (datasize))))
  let imm := imm
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3926)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    match sh with
    | 0 => (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked (datasize))))
    | _ =>
      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (imm12 +++ (Zeros (n := 12)))
        (Sail.Int.toNatChecked (datasize))))
  let imm := imm
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3927)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    match sh with
    | 0 => (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked (datasize))))
    | _ =>
      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (imm12 +++ (Zeros (n := 12)))
        (Sail.Int.toNatChecked (datasize))))
  let imm := imm
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    setflags sub_op)


def decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op))


def decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op))


def decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op))


def decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op))


def decode_addg_aarch64_instrs_integer_tags_mcaddtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (uimm4 : (BitVec 4)) (op3 : (BitVec 2)) (uimm6 : (BitVec 6)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Xd)
      let n : Int := (BitVec.toNat Xn)
      let tag_offset : (BitVec 4) := uimm4
      let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend uimm6 64) <<< LOG2_TAG_GRANULE)
      let ADD : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcaddtag ADD (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) offset tag_offset))


def decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let page : Bool := (op == 1#1)
  let imm ← (( do (undefined_bitvector_at (← occLabel 3940) 64) ) : SailM (BitVec 64) )
  let imm : (BitVec 64) :=
    if (page : Bool)
    then (sign_extend ((immhi +++ immlo) +++ (Zeros (n := 12))) 64)
    else (sign_extend (immhi +++ immlo) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_address_pc_rel (Sail.Int.toNatChecked (d)) imm page)


end ArmFull.Functions
