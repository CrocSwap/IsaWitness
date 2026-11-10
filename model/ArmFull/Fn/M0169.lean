import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0046
import ArmFull.Fn.M0098
import ArmFull.Fn.M0112
import ArmFull.Fn.M0115
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0153
import ArmFull.Fn.M0158
import ArmFull.Fn.M0159
import ArmFull.Fn.M0164

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

def AArch32_TLBContextEL30 (va : (BitVec 32)) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2533) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := SS_Secure }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL30 }
  let w__0 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  let tlbcontext ← (( do
    if (((_get_TTBCR_Type_EAE w__0) == 1#1) : Bool)
    then
      (do
        let w__1 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
        let w__4 ← (( do
          if (((_get_TTBCR_Type_A1 w__1) == 0#1) : Bool)
          then
            (do
              let w__2 ← (( do readReg TTBR0_S ) : SailM (BitVec 64) )
              (pure ((_get_TTBR0_Type_ASID w__2))))
          else
            (do
              let w__3 ← (( do readReg TTBR1_S ) : SailM (BitVec 64) )
              (pure ((_get_TTBR1_Type_ASID w__3)))) ) : SailM (BitVec 8) )
        let tlbcontext :=
          ({ tlbcontext with asid := (Sail.BitVec.zeroExtend w__4 16) } : TLBContext)
        (pure (tlbcontext)))
    else
      (do
        let w__5 ← (( do readReg CONTEXTIDR_S ) : SailM (BitVec 32) )
        let tlbcontext :=
          ({ tlbcontext with asid := (Sail.BitVec.zeroExtend (_get_CONTEXTIDR_Type_ASID w__5) 16) } : TLBContext)
        (pure (tlbcontext))) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with tg := TGx_4KB }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend va 64) }
  let w__8 ← (( do
    if ((← do
         (HaveCommonNotPrivateTransExt ())) : Bool)
    then
      (do
        let w__7 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
        (pure ((((_get_TTBCR_Type_EAE w__7) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      let w__9 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let w__10 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let w__11 ← (( do
        (AArch32_GetVARange va (_get_TTBCR_Type_T0SZ w__9) (_get_TTBCR_Type_T1SZ w__10)) ) : SailM
        VARange )
      if ((BEq.beq w__11 VARange_LOWER) : Bool)
      then
        (do
          let w__12 ← (( do readReg TTBR0_S ) : SailM (BitVec 64) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR0_Type_CnP w__12) } : TLBContext)
          (pure (tlbcontext)))
      else
        (do
          let w__13 ← (( do readReg TTBR1_S ) : SailM (BitVec 64) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR1_Type_CnP w__13) } : TLBContext)
          (pure (tlbcontext))))
  else
    (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
    (pure (tlbcontext)))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV85 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap5_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV84 enabled))
  else (pure (()))


def A32ExpandImm (imm12 : (BitVec 12)) : SailM (BitVec 32) := do
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 2699) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (__tup_0, _) ← (( do (A32ExpandImm_C imm12 w__0.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  (pure (__tup_0))


/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegReadCanWriteAPSR (cp_num : Int) (instr : (BitVec 32)) : SailM Bool := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  ArmFull.assert w__0 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42703.25-42703.26"
  ArmFull.assert ((cp_num == 14) || (cp_num == 15)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42704.38-42704.39"
  ArmFull.assert (cp_num == (BitVec.toNat (Sail.BitVec.extractLsb instr 11 8))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42705.41-42705.42"
  let opc1 : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 23 21))
  let opc2 : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 7 5))
  let CRn : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 19 16))
  let CRm : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 3 0))
  (pure (if ((((((cp_num == 14) && (opc1 == 0)) && (CRn == 0)) && (CRm == 1)) && (opc2 == 0)) : Bool)
    then true
    else false))


/-- Type quantifiers: t : Int -/
def TLBI_PAALLOS_SysOpsWrite_b02935bd045e4472 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_TLBI_PAALL Shareability_OSH))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_PAALL_SysOpsWrite_30c81768c02bd90b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_TLBI_PAALL Shareability_NSH))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RPALOS_SysOpsWrite_a11d11817d32a6eb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RPA TLBILevel_Last w__1 Shareability_OSH))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RPAOS_SysOpsWrite_a15697b49d6ed58f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RPA TLBILevel_Any w__1 Shareability_OSH))
              else (pure (())))))


def decode_abs_aarch64_instrs_integer_arithmetic_unary_abs (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_unary_abs (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


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
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    setflags sub_op)


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_amount :
  Nat, k_sub_op : Bool, 0 ≤ shift_amount ∧
  shift_amount ≤ 63 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) (sub_op : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3918)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (ShiftReg m shift_type shift_amount datasize)) ) : SailM
    (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3919) 4) ) : SailM (BitVec 4) )
  let carry_in ← (( do (undefined_bitvector_at (← occLabel 3920) 1) ) : SailM (BitVec 1) )
  let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
    if (sub_op : Bool)
    then
      (let operand2 : (BitVec datasize) := (Complement.complement operand2)
      let carry_in : (BitVec 1) := 1#1
      (carry_in, operand2))
    else
      (let carry_in : (BitVec 1) := 0#1
      (carry_in, operand2))
  let (tup__0, tup__1) :=
    ((AddWithCarry operand1 operand2 carry_in) : ((BitVec datasize) × (BitVec 4)))
  let result : (BitVec datasize) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  (X_set d datasize (Sail.BitVec.castWidth result))


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
  (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    setflags sub_op)


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, shift : Nat, k_sub_op
  : Bool, List.elem shift [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (d : Nat) (datasize : Nat) (extend_type : ExtendType) (m : Nat) (n : Nat) (setflags : Bool) (shift : Nat) (sub_op : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3928)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        let w__0 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
        (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)))))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (X_read n datasize))) ) : SailM (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (ExtendReg m extend_type shift datasize)) ) :
    SailM (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3929) 4) ) : SailM (BitVec 4) )
  let carry_in ← (( do (undefined_bitvector_at (← occLabel 3930) 1) ) : SailM (BitVec 1) )
  let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
    if (sub_op : Bool)
    then
      (let operand2 : (BitVec datasize) := (Complement.complement operand2)
      let carry_in : (BitVec 1) := 1#1
      (carry_in, operand2))
    else
      (let carry_in : (BitVec 1) := 0#1
      (carry_in, operand2))
  let (tup__0, tup__1) :=
    ((AddWithCarry operand1 operand2 carry_in) : ((BitVec datasize) × (BitVec 4)))
  let result : (BitVec datasize) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  if (((d == 31) && (! setflags)) : Bool)
  then
    (do
      (SP_set (Sail.BitVec.zeroExtend result 64)))
  else
    (do
      (X_set d datasize (Sail.BitVec.castWidth result)))


def decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let page : Bool := (op == 1#1)
  let imm ← (( do (undefined_bitvector_at (← occLabel 3940) 64) ) : SailM (BitVec 64) )
  let imm : (BitVec 64) :=
    if (page : Bool)
    then (sign_extend ((immhi +++ immlo) +++ (Zeros (n := 12))) 64)
    else (sign_extend (immhi +++ immlo) 64)
  (execute_aarch64_instrs_integer_arithmetic_address_pc_rel (Sail.Int.toNatChecked (d)) imm page)


def decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let page : Bool := (op == 1#1)
  let imm ← (( do (undefined_bitvector_at (← occLabel 3941) 64) ) : SailM (BitVec 64) )
  let imm : (BitVec 64) :=
    if (page : Bool)
    then (sign_extend ((immhi +++ immlo) +++ (Zeros (n := 12))) 64)
    else (sign_extend (immhi +++ immlo) 64)
  (execute_aarch64_instrs_integer_arithmetic_address_pc_rel (Sail.Int.toNatChecked (d)) imm page)


def decode_and_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3944) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3945) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3946)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
  (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n)) op
    setflags)


def decode_ands_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3947) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3948) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3949)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
  (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n)) op
    setflags)


def decode_eor_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3950) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3951) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3952)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
  (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n)) op
    setflags)


end ArmFull.Functions
