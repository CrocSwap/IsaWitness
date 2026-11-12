import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0141
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0173
import ArmFull.Fn.M0175
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0195
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0242
import ArmFull.Fn.M0253
import ArmFull.Fn.M0852
import ArmFull.Fn.M1003
import ArmFull.Fn.M1142
import ArmFull.Fn.M1148

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

/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wordhigher : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STM_u_Op_AS_txt (increment_name : Bool) (n : Nat) (registers : (BitVec 16)) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 3791) 32) ) : SailM (BitVec 32) )
  let length ← (( do (undefined_int_at (← occLabel 3792) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let length : Int := (4 *i (BitCount registers))
          let w__6 ← (( do
            if (increment_name : Bool)
            then
              (do
                (R_read n))
            else
              (do
                let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
                (pure ((BitVec.subInt w__5 length)))) ) : SailM (BitVec 32) )
          let address : (BitVec 32) := (w__6 : (BitVec 32))
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let address ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 14
            (do
              let mut loop_vars := address
              for i in [loop_i_lower:loop_i_upper:1]i do
                let address := loop_vars
                loop_vars ← do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                           (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
                  then
                    (do
                      let w__7 ← (( do (Rmode_read i M32_User) ) : SailM (BitVec 32) )
                      (MemS_set address 4 w__7)
                      let address : (BitVec 32) := (BitVec.addInt address 4)
                      (pure (address)))
                  else (pure (address))
              (pure loop_vars)) ) : SailM (BitVec 32) )
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
          then
            (do
              let w__8 ← (( do (PCStoreValue ()) ) : SailM (BitVec 32) )
              (MemS_set address 4 w__8))
          else (pure (()))))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDA_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
  let w__0 ← (( do (MemO_read address 4) ) : SailM (BitVec (8 * 4)) )
  (R_set t w__0)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
  let w__0 ← (( do (MemO_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__0 32))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEX_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 4)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
  let w__0 ← (( do (MemO_read address 4) ) : SailM (BitVec (8 * 4)) )
  (R_set t w__0)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEXB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 1)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
  let w__0 ← (( do (MemO_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__0 32))


/-- Type quantifiers: n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEXD_Op_A_txt (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 8)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 8 false t true)
  let value_name ← (( do (MemO_read address 8) ) : SailM (BitVec 64) )
  let w__0 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
  let w__1 : (BitVec 32) :=
    if (w__0 : Bool)
    then (Sail.BitVec.extractLsb value_name 63 32)
    else (Sail.BitVec.extractLsb value_name 31 0)
  (R_set t w__1)
  let w__2 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
  let w__3 : (BitVec 32) :=
    if (w__2 : Bool)
    then (Sail.BitVec.extractLsb value_name 31 0)
    else (Sail.BitVec.extractLsb value_name 63 32)
  (R_set t2 w__3)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEXH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 2)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
  let w__0 ← (( do (MemO_read address 2) ) : SailM (BitVec (8 * 2)) )
  (R_set t (Sail.BitVec.zeroExtend w__0 32))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
  let w__0 ← (( do (MemO_read address 2) ) : SailM (BitVec (8 * 2)) )
  (R_set t (Sail.BitVec.zeroExtend w__0 32))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STL_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
  let w__0 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemO_set address 4 w__0)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STLB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
  let w__0 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemO_set address 1 (Sail.BitVec.extractLsb w__0 7 0))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEX_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (AArch32_ExclusiveMonitorsPass address 4) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemO_set address 4 w__1)
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEXB_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (AArch32_ExclusiveMonitorsPass address 1) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemO_set address 1 (Sail.BitVec.extractLsb w__1 7 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEXD_Op_A_txt (d : Nat) (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
  let value_name ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
        let w__2 ← (( do (R_read t2) ) : SailM (BitVec 32) )
        (pure ((w__1 +++ w__2))))
    else
      (do
        let w__3 ← (( do (R_read t2) ) : SailM (BitVec 32) )
        let w__4 ← (( do (R_read t) ) : SailM (BitVec 32) )
        (pure ((w__3 +++ w__4)))) ) : SailM (BitVec 64) )
  let w__5 ← (( do (AArch32_ExclusiveMonitorsPass address 8) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 8 false t true)
      (MemO_set address 8 value_name)
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEXH_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (AArch32_ExclusiveMonitorsPass address 2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemO_set address 2 (Sail.BitVec.extractLsb w__1 15 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STLH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
  let w__0 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemO_set address 2 (Sail.BitVec.extractLsb w__0 15 0))


def decode_aarch32_instrs_VMMLA_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Nat := 2
  (execute_aarch32_instrs_VMMLA_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_aarch32_instrs_VMMLA_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Nat := 2
  (execute_aarch32_instrs_VMMLA_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_add_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  ArmFull.assert (datasize ≥b esize) "sail-arm/instrs64.sail:1153.42-1153.43"
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce op operand esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_add_simd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce op operand esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


def decode_bfmmla_advsimd_aarch64_instrs_vector_bfmmla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_bfmmla (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_cpy (d : Nat) (n : Nat) (options_name : (BitVec 4)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let N ← (( do (MaxBlockSizeCopiedBytes ()) ) : SailM Nat )
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let fromaddress ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let cpysize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let nzcv : (BitVec 4) := (w__0.N +++ (w__1.Z +++ (w__2.C +++ w__3.V)))
  let stagecpysize ← (( do (undefined_bitvector_at (← occLabel 4056) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4057)
      (Sail.Int.toNatChecked ((8 *i N))))) ) : SailM (BitVec (8 * (Sail.Int.toNatChecked N))) )
  let B ← (( do (undefined_int_at (← occLabel 4058) ()) ) : SailM Int )
  let supports_option_a ← (( do (CPYOptionA ()) ) : SailM Bool )
  let rprivileged ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 1)])) == 1#1) : Bool)
    then
      (do
        (AArch64_IsUnprivAccessPriv ()))
    else
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((w__5.EL != EL0)))) ) : SailM Bool )
  let wprivileged ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 0)])) == 1#1) : Bool)
    then
      (do
        (AArch64_IsUnprivAccessPriv ()))
    else
      (do
        let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((w__7.EL != EL0)))) ) : SailM Bool )
  let rnontemporal : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 3)])) == 1#1)
  let wnontemporal : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access options_name 2)])) == 1#1)
  let raccdesc ← (( do (CreateAccDescMOPS MemOp_LOAD rprivileged rnontemporal) ) : SailM
    AccessDescriptor )
  let waccdesc ← (( do (CreateAccDescMOPS MemOp_STORE wprivileged wnontemporal) ) : SailM
    AccessDescriptor )
  let (cpysize, fromaddress, nzcv, stagecpysize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let cpysize : (BitVec 64) :=
          if (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb cpysize 63 55)) != 0b000000000#9) : Bool)
          then 0x007FFFFFFFFFFFFF#64
          else cpysize
        let forward ← (( do (undefined_bool_at (← occLabel 4059) ()) ) : SailM Bool )
        let forward ← (( do
          if ((((BitVec.toNat (Sail.BitVec.extractLsb fromaddress 55 0)) >b (BitVec.toNat
                   (Sail.BitVec.extractLsb toaddress 55 0))) && (((BitVec.toNat
                   (Sail.BitVec.extractLsb fromaddress 55 0)) <b (BitVec.toNat
                   ((Sail.BitVec.castWidth (m := 56) (Sail.BitVec.extractLsb toaddress 55 0)) + (Sail.BitVec.castWidth (m := 56) (Sail.BitVec.extractLsb
                       cpysize 55 0))))) : Bool)) : Bool)
          then (pure (true))
          else
            (do
              if ((((BitVec.toNat (Sail.BitVec.extractLsb fromaddress 55 0)) <b (BitVec.toNat
                       (Sail.BitVec.extractLsb toaddress 55 0))) && (((BitVec.toNat
                       ((Sail.BitVec.castWidth (m := 56) (Sail.BitVec.extractLsb fromaddress 55 0)) + (Sail.BitVec.castWidth (m := 56) (Sail.BitVec.extractLsb
                           cpysize 55 0)))) >b (BitVec.toNat (Sail.BitVec.extractLsb toaddress 55 0))) : Bool)) : Bool)
              then (pure (false))
              else
                (do
                  (MemCpyDirectionChoice fromaddress toaddress cpysize))) ) : SailM Bool )
        let (cpysize, fromaddress, nzcv, toaddress) : ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let (cpysize, fromaddress, toaddress) : ((BitVec 64) × (BitVec 64) × (BitVec 64)) :=
              if (forward : Bool)
              then
                (let toaddress : (BitVec 64) := (toaddress + cpysize)
                let fromaddress : (BitVec 64) := (fromaddress + cpysize)
                let cpysize : (BitVec 64) :=
                  ((Sail.BitVec.castWidth (m := 64) (Zeros (n := 64))) - cpysize)
                (cpysize, fromaddress, toaddress))
              else (cpysize, fromaddress, toaddress)
            (cpysize, fromaddress, nzcv, toaddress))
          else
            (let (fromaddress, nzcv, toaddress) : ((BitVec 64) × (BitVec 4) × (BitVec 64)) :=
              if ((! forward) : Bool)
              then
                (let toaddress : (BitVec 64) := (toaddress + cpysize)
                let fromaddress : (BitVec 64) := (fromaddress + cpysize)
                let nzcv : (BitVec 4) := 0b1010#4
                (fromaddress, nzcv, toaddress))
              else
                (let nzcv : (BitVec 4) := 0b0010#4
                (fromaddress, nzcv, toaddress))
            (cpysize, fromaddress, nzcv, toaddress))
        let w__9 ← (( do (CPYPreSizeChoice toaddress fromaddress cpysize) ) : SailM (BitVec 64) )
        let stagecpysize := (w__9 : (BitVec 64))
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access stagecpysize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                cpysize 63)]))) || (stagecpysize == (Sail.BitVec.castWidth (m := 64) (Zeros
              (n := 64))))) "armcert/armcert_c27.sail:450.78-450.79"
        if (((BitVec.toInt cpysize) >b 0) : Bool)
        then
          (do
            ArmFull.assert ((BitVec.toInt stagecpysize) ≤b (BitVec.toInt cpysize)) "armcert/armcert_c27.sail:452.54-452.55")
        else
          (do
            ArmFull.assert ((BitVec.toInt stagecpysize) ≥b (BitVec.toInt cpysize)) "armcert/armcert_c27.sail:454.54-454.55")
        (pure ((cpysize, fromaddress, nzcv, stagecpysize, toaddress))))
    else
      (do
        let zero_size_exceptions ← (( do (MemCpyZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt cpysize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)])) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue
                      options_name))
                else (pure (())))
            else
              (do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)])) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue
                      options_name))
                else (pure (()))))
        else (pure (()))
        let postsize ← (( do (CPYPostSizeChoice toaddress fromaddress cpysize) ) : SailM
          (BitVec 64) )
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access postsize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                cpysize 63)]))) || (((BitVec.toInt postsize) == 0) : Bool)) "armcert/armcert_c27.sail:476.68-476.69"
        let stagecpysize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagecpysize : (BitVec 64) := (cpysize - postsize)
              let w__10 ← (( do (MemCpyParametersIllformedM toaddress fromaddress cpysize) ) :
                SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue
                    options_name))
              else (pure (()))
              (pure (stagecpysize)))
          else
            (do
              let stagecpysize : (BitVec 64) := postsize
              let w__12 ← (( do
                if (((cpysize != postsize) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    (MemCpyParametersIllformedE toaddress fromaddress cpysize)) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue
                    options_name))
              else (pure (()))
              (pure (stagecpysize))) ) : SailM (BitVec 64) )
        (pure ((cpysize, fromaddress, nzcv, stagecpysize, toaddress)))) ) : SailM
    ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × (BitVec 64)) )
  let w__13 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      (SPESampleMemCopy ()))
  else (pure (()))
  let (cpysize, fromaddress, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, cpysize, readdata, stagecpysize) ← (( do
          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (B, cpysize, readdata, stagecpysize) => (pure ((BitVec.toInt
                stagecpysize) != 0))) (B, cpysize, readdata, stagecpysize)
            fun (B, cpysize, readdata, stagecpysize) => do
              let w__14 ← (( do
                (CPYSizeChoice toaddress fromaddress cpysize
                  (if (((BitVec.toInt stagecpysize) <b 0) : Bool)
                  then (Neg.neg (BitVec.toInt stagecpysize))
                  else (BitVec.toInt stagecpysize)) N) ) : SailM Int )
              let B : Int := (w__14 : Int)
              let B : Int := B
              let (cpysize, readdata, stagecpysize) ← (( do
                if (((BitVec.toInt cpysize) <b 0) : Bool)
                then
                  (do
                    ArmFull.assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagecpysize))) "armcert/armcert_c27.sail:504.64-504.65"
                    ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:505.80-505.81"
                    let w__15 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Mem_read (fromaddress + cpysize)
                        (Sail.Int.toNatChecked (B)) raccdesc)) ) : SailM
                      (BitVec (Sail.Int.toNatChecked ((B : Int) *i (8 : Int)))) )
                    let readdata :=
                      ((Sail.BitVec.updateSubrange readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0 (Sail.BitVec.castWidth w__15)) : (BitVec (8 * (Sail.Int.toNatChecked N))))
                    (Mem_set (toaddress + cpysize) (Sail.Int.toNatChecked (B)) waccdesc
                      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0)))
                    let cpysize : (BitVec 64) := (BitVec.addInt cpysize B)
                    let stagecpysize : (BitVec 64) := (BitVec.addInt stagecpysize B)
                    (pure ((cpysize, readdata, stagecpysize))))
                else
                  (do
                    ArmFull.assert (B ≤b (BitVec.toInt stagecpysize)) "armcert/armcert_c27.sail:511.52-511.53"
                    let cpysize : (BitVec 64) := (BitVec.subInt cpysize B)
                    let stagecpysize : (BitVec 64) := (BitVec.subInt stagecpysize B)
                    ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:514.80-514.81"
                    let w__16 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Mem_read (fromaddress + cpysize)
                        (Sail.Int.toNatChecked (B)) raccdesc)) ) : SailM
                      (BitVec (Sail.Int.toNatChecked ((B : Int) *i (8 : Int)))) )
                    let readdata :=
                      ((Sail.BitVec.updateSubrange readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0 (Sail.BitVec.castWidth w__16)) : (BitVec (8 * (Sail.Int.toNatChecked N))))
                    (Mem_set (toaddress + cpysize) (Sail.Int.toNatChecked (B)) waccdesc
                      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0)))
                    (pure ((cpysize, readdata, stagecpysize)))) ) : SailM
                ((BitVec 64) × (BitVec (8 * (Sail.Int.toNatChecked N))) × (BitVec 64)) )
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 cpysize))
              else (pure (()))
              (pure ((B, cpysize, readdata, stagecpysize)))
          (pure loop_vars) ) : SailM
          (Int × (BitVec 64) × (BitVec (8 * (Sail.Int.toNatChecked N))) × (BitVec 64)) )
        (pure ((cpysize, fromaddress, toaddress))))
    else
      (do
        let (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) ← (( do
          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) => (pure ((BitVec.toNat
                stagecpysize) >b 0))) (B, cpysize, fromaddress, readdata, stagecpysize, toaddress)
            fun (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) => do
              let w__17 ← (( do
                (CPYSizeChoice toaddress fromaddress cpysize (BitVec.toNat stagecpysize) N) ) :
                SailM Int )
              let B : Int := (w__17 : Int)
              ArmFull.assert (B ≤b (BitVec.toNat stagecpysize)) "armcert/armcert_c27.sail:527.42-527.43"
              let B : Int := B
              let (fromaddress, readdata, toaddress) ← (( do
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 3)])) == 0#1) : Bool)
                then
                  (do
                    ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:531.80-531.81"
                    let w__18 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Mem_read fromaddress
                        (Sail.Int.toNatChecked (B)) raccdesc)) ) : SailM
                      (BitVec (Sail.Int.toNatChecked ((B : Int) *i (8 : Int)))) )
                    let readdata :=
                      ((Sail.BitVec.updateSubrange readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0 (Sail.BitVec.castWidth w__18)) : (BitVec (8 * (Sail.Int.toNatChecked N))))
                    (Mem_set toaddress (Sail.Int.toNatChecked (B)) waccdesc
                      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0)))
                    let fromaddress : (BitVec 64) := (BitVec.addInt fromaddress B)
                    let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
                    (pure ((fromaddress, readdata, toaddress))))
                else
                  (do
                    ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:537.80-537.81"
                    let w__19 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Mem_read (BitVec.subInt fromaddress B)
                        (Sail.Int.toNatChecked (B)) raccdesc)) ) : SailM
                      (BitVec (Sail.Int.toNatChecked ((B : Int) *i (8 : Int)))) )
                    let readdata :=
                      ((Sail.BitVec.updateSubrange readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0 (Sail.BitVec.castWidth w__19)) : (BitVec (8 * (Sail.Int.toNatChecked N))))
                    (Mem_set (BitVec.subInt toaddress B) (Sail.Int.toNatChecked (B)) waccdesc
                      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb readdata
                        (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0)))
                    let fromaddress : (BitVec 64) := (BitVec.subInt fromaddress B)
                    let toaddress : (BitVec 64) := (BitVec.subInt toaddress B)
                    (pure ((fromaddress, readdata, toaddress)))) ) : SailM
                ((BitVec 64) × (BitVec (8 * (Sail.Int.toNatChecked N))) × (BitVec 64)) )
              let cpysize : (BitVec 64) := (BitVec.subInt cpysize B)
              let stagecpysize : (BitVec 64) := (BitVec.subInt stagecpysize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 cpysize)
                  (X_set d 64 toaddress)
                  (X_set s 64 fromaddress))
              else (pure (()))
              (pure ((B, cpysize, fromaddress, readdata, stagecpysize, toaddress)))
          (pure loop_vars) ) : SailM
          (Int × (BitVec 64) × (BitVec 64) × (BitVec (8 * (Sail.Int.toNatChecked N))) × (BitVec 64) × (BitVec 64))
          )
        (pure ((cpysize, fromaddress, toaddress)))) ) : SailM
    ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 cpysize)
      (X_set d 64 toaddress)
      (X_set s 64 fromaddress)
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__20 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__21 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__22 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__23 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


end ArmFull.Functions
