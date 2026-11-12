import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0049
import ArmFull.Fn.M0061
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0118
import ArmFull.Fn.M0141
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0173
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0215
import ArmFull.Fn.M0237
import ArmFull.Fn.M0238
import ArmFull.Fn.M0242
import ArmFull.Fn.M0253
import ArmFull.Fn.M0257
import ArmFull.Fn.M0258
import ArmFull.Fn.M0852
import ArmFull.Fn.M1142
import ArmFull.Fn.M1150

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

/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_cpyf (d : Nat) (n : Nat) (options_name : (BitVec 4)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let N ← (( do (MaxBlockSizeCopiedBytes ()) ) : SailM Nat )
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let fromaddress ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let cpysize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let nzcv : (BitVec 4) := (w__0.N +++ (w__1.Z +++ (w__2.C +++ w__3.V)))
  let stagecpysize ← (( do (undefined_bitvector_at (← occLabel 4076) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4077)
      (Sail.Int.toNatChecked ((8 *i N))))) ) : SailM (BitVec (8 * (Sail.Int.toNatChecked N))) )
  let B ← (( do (undefined_int_at (← occLabel 4078) ()) ) : SailM Int )
  let supports_option_a ← (( do (CPYFOptionA ()) ) : SailM Bool )
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
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cpysize 63)])) == 1#1) : Bool)
          then 0x7FFFFFFFFFFFFFFF#64
          else cpysize
        let (cpysize, fromaddress, nzcv, toaddress) : ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let toaddress : (BitVec 64) := (toaddress + cpysize)
            let fromaddress : (BitVec 64) := (fromaddress + cpysize)
            let cpysize : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Zeros (n := 64))) - cpysize)
            (cpysize, fromaddress, nzcv, toaddress))
          else
            (let nzcv : (BitVec 4) := 0b0010#4
            (cpysize, fromaddress, nzcv, toaddress))
        let w__8 ← (( do (CPYPreSizeChoice toaddress fromaddress cpysize) ) : SailM (BitVec 64) )
        let stagecpysize := (w__8 : (BitVec 64))
        ArmFull.assert (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access stagecpysize 63)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                cpysize 63)]))) || (stagecpysize == (Sail.BitVec.castWidth (m := 64) (Zeros
              (n := 64))))) "armcert/armcert_c27.sail:603.78-603.79"
        if (((BitVec.toInt cpysize) >b 0) : Bool)
        then
          (do
            ArmFull.assert ((BitVec.toInt stagecpysize) ≤b (BitVec.toInt cpysize)) "armcert/armcert_c27.sail:605.54-605.55")
        else
          (do
            ArmFull.assert ((BitVec.toInt stagecpysize) ≥b (BitVec.toInt cpysize)) "armcert/armcert_c27.sail:607.54-607.55")
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
                cpysize 63)]))) || (((BitVec.toInt postsize) == 0) : Bool)) "armcert/armcert_c27.sail:629.68-629.69"
        let stagecpysize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagecpysize : (BitVec 64) := (cpysize - postsize)
              let w__9 ← (( do (MemCpyParametersIllformedM toaddress fromaddress cpysize) ) :
                SailM Bool )
              if (w__9 : Bool)
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
              let w__11 ← (( do
                if (((cpysize != postsize) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    (MemCpyParametersIllformedE toaddress fromaddress cpysize)) ) : SailM Bool )
              if (w__11 : Bool)
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
  let w__12 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__12 : Bool)
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
              let w__13 ← (( do
                (CPYSizeChoice toaddress fromaddress cpysize
                  (if (((BitVec.toInt stagecpysize) <b 0) : Bool)
                  then (Neg.neg (BitVec.toInt stagecpysize))
                  else (BitVec.toInt stagecpysize)) N) ) : SailM Int )
              let B : Int := (w__13 : Int)
              ArmFull.assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagecpysize))) "armcert/armcert_c27.sail:654.54-654.55"
              let B : Int := B
              ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:657.76-657.77"
              let w__14 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Mem_read (fromaddress + cpysize)
                  (Sail.Int.toNatChecked (B)) raccdesc)) ) : SailM
                (BitVec (Sail.Int.toNatChecked ((B : Int) *i (8 : Int)))) )
              let readdata :=
                ((Sail.BitVec.updateSubrange readdata (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0
                  (Sail.BitVec.castWidth w__14)) : (BitVec (8 * (Sail.Int.toNatChecked N))))
              let B : Int := B
              ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:662.76-662.77"
              (Mem_set (toaddress + cpysize) (Sail.Int.toNatChecked (B)) waccdesc
                (Sail.BitVec.castWidth (Sail.BitVec.extractLsb readdata
                  (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0)))
              let cpysize : (BitVec 64) := (BitVec.addInt cpysize B)
              let stagecpysize : (BitVec 64) := (BitVec.addInt stagecpysize B)
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
              let w__15 ← (( do
                (CPYSizeChoice toaddress fromaddress cpysize (BitVec.toNat stagecpysize) N) ) :
                SailM Int )
              let B : Int := (w__15 : Int)
              ArmFull.assert (B ≤b (BitVec.toNat stagecpysize)) "armcert/armcert_c27.sail:675.42-675.43"
              let B : Int := B
              ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:678.76-678.77"
              let w__16 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Mem_read fromaddress (Sail.Int.toNatChecked (B))
                  raccdesc)) ) : SailM (BitVec (Sail.Int.toNatChecked ((B : Int) *i (8 : Int)))) )
              let readdata :=
                ((Sail.BitVec.updateSubrange readdata (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0
                  (Sail.BitVec.castWidth w__16)) : (BitVec (8 * (Sail.Int.toNatChecked N))))
              let B : Int := B
              ArmFull.assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "armcert/armcert_c27.sail:683.76-683.77"
              (Mem_set toaddress (Sail.Int.toNatChecked (B)) waccdesc
                (Sail.BitVec.castWidth (Sail.BitVec.extractLsb readdata
                  (Sail.Int.toNatChecked (((B *i 8) -i 1))) 0)))
              let fromaddress : (BitVec 64) := (BitVec.addInt fromaddress B)
              let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
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
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__17 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__20 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_add_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  ArmFull.assert (datasize ≥b esize) "sail-arm/instrs64.sail:12626.42-12626.43"
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce op operand esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


def decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_max_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  ArmFull.assert (datasize ≥b esize) "sail-arm/instrs64.sail:18641.42-18641.43"
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce op operand esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_max_simd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce op operand esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


/-- Type quantifiers: k_is_gcssttr : Bool, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_gcs_general_register (is_gcssttr : Bool) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4333) 64) ) : SailM (BitVec 64) )
  let w__1 ← (( do
    if (((! is_gcssttr) : Bool) : Bool)
    then (pure true)
    else
      (do
        (AArch64_IsUnprivAccessPriv ())) ) : SailM Bool )
  let effective_el ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (w__2.EL)))
    else (pure (EL0)) ) : SailM (BitVec 2) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((effective_el == w__3.EL) : Bool)
  then
    (do
      (CheckGCSSTREnabled ()))
  else (pure (()))
  let accdesc ← (( do (CreateAccDescGCS effective_el MemOp_STORE) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  (Mem_set address 8 accdesc data)


/-- Type quantifiers: datasize : Nat, esize : Nat, index : Int, m : Int, n : Nat, k_nontemporal :
  Bool, k_replicate : Bool, selem : Nat, t__arg : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤
  t__arg ∧
  t__arg ≤ 31 ∧
  List.elem selem [1, 2, 3, 4] ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_memory_vector_single_no_wb (datasize : Nat) (esize : Nat) (index : Int) (m : Int) (memop : MemOp) (n : Nat) (nontemporal : Bool) (replicate : Bool) (selem : Nat) (t__arg : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let t : Int := t__arg
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4335) 64) ) : SailM (BitVec 64) )
  let rval ← (( do (undefined_bitvector_at (← occLabel 4336) 128) ) : SailM (BitVec 128) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4337)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let ebytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let offs : (BitVec 64) := (Zeros (n := 64))
  let offs ← (( do
    if (replicate : Bool)
    then
      (do
        let (element, offs, t) ← (( do
          let loop_s_lower : Nat := 0
          let loop_s_upper : Nat := (Sail.Int.toNatChecked ((selem -i 1)))
          (do
            let mut loop_vars := (element, offs, t)
            for s in [loop_s_lower:loop_s_upper:1]i do
              let (element, offs, t) := loop_vars
              loop_vars ← do
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Mem_read (address + offs) ebytes accdesc)) ) :
                  SailM (BitVec (esize / 8 * 8)) )
                let element := ((Sail.BitVec.castWidth w__2) : (BitVec esize))
                (V_set t datasize
                  (Sail.BitVec.castWidth (BitVec.replicateBits element
                    (Sail.Int.toNatChecked ((Int.ediv datasize esize))))))
                let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
                let t : Int := (fmod_int (t +i 1) 32)
                (pure ((element, offs, t)))
            (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 64) × Int) )
        (pure (offs)))
    else
      (do
        let (offs, rval, t) ← (( do
          let loop_s_lower : Nat := 0
          let loop_s_upper : Nat := (Sail.Int.toNatChecked ((selem -i 1)))
          (do
            let mut loop_vars := (offs, rval, t)
            for s in [loop_s_lower:loop_s_upper:1]i do
              let (offs, rval, t) := loop_vars
              loop_vars ← do
                let w__3 ← (( do (V_read t 128) ) : SailM (BitVec 128) )
                let rval := (w__3 : (BitVec 128))
                let rval ← (( do
                  if ((BEq.beq memop MemOp_LOAD) : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Mem_read (address + offs) ebytes accdesc)) )
                        : SailM (BitVec (esize / 8 * 8)) )
                      let w__5 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_set rval index esize
                          (Sail.BitVec.castWidth w__4))) ) : SailM (BitVec 128) )
                      let rval := (w__5 : (BitVec 128))
                      (V_set t 128 rval)
                      (pure (rval)))
                  else
                    (do
                      let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read rval index esize))
                        ) : SailM (BitVec ((Sail.Int.toNatChecked ebytes) * 8)) )
                      (Mem_set (address + offs) ebytes accdesc (Sail.BitVec.castWidth w__6))
                      (pure (rval))) ) : SailM (BitVec 128) )
                let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
                let t : Int := (fmod_int (t +i 1) 32)
                (pure ((offs, rval, t)))
            (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 128) × Int) )
        (pure (offs))) ) : SailM (BitVec 64) )
  let w__7 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))
  if (wback : Bool)
  then
    (do
      let offs ← (( do
        if ((m != 31) : Bool)
        then
          (do
            (X_read m 64))
        else (pure (offs)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set (address + offs)))
      else
        (do
          (X_set n 64 (address + offs))))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, elements : Int, esize : Nat, m : Int, n : Nat, k_nontemporal :
  Bool, rpt : Nat, selem : Nat, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem selem [1, 2, 3, 4] ∧
  List.elem rpt [1, 2, 3, 4] ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_memory_vector_multiple_no_wb (datasize : Nat) (elements : Int) (esize : Nat) (m : Int) (memop : MemOp) (n : Nat) (nontemporal : Bool) (rpt : Nat) (selem : Nat) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4362) 64) ) : SailM (BitVec 64) )
  let rval ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4363)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let tt ← (( do (undefined_int_at (← occLabel 4364) ()) ) : SailM Int )
  let ebytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let offs : (BitVec 64) := (Zeros (n := 64))
  let (offs, rval, tt) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((rpt -i 1)))
    (do
      let mut loop_vars := (offs, rval, tt)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (offs, rval, tt) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (offs, rval, tt)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (offs, rval, tt) := loop_vars_1
              loop_vars_1 ← do
                let tt : Int := (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32)
                let loop_s_lower : Nat := 0
                let loop_s_upper : Nat := (Sail.Int.toNatChecked ((selem -i 1)))
                (do
                  let mut loop_vars_2 := (offs, rval, tt)
                  for s in [loop_s_lower:loop_s_upper:1]i do
                    let (offs, rval, tt) := loop_vars_2
                    loop_vars_2 ← do
                      let tt : Int := tt
                      let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read tt datasize)) ) :
                        SailM (BitVec datasize) )
                      let rval := (w__2 : (BitVec datasize))
                      let tt : Int := tt
                      let rval ← (( do
                        if ((BEq.beq memop MemOp_LOAD) : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Mem_read (address + offs) ebytes
                                accdesc)) ) : SailM (BitVec (esize / 8 * 8)) )
                            let w__4 ← (( do (Elem_set rval e esize (Sail.BitVec.castWidth w__3))
                              ) : SailM (BitVec datasize) )
                            let rval := (w__4 : (BitVec datasize))
                            (V_set tt datasize (Sail.BitVec.castWidth rval))
                            (pure (rval)))
                        else
                          (do
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read rval e esize)) ) : SailM
                              (BitVec ((Sail.Int.toNatChecked ebytes) * 8)) )
                            (Mem_set (address + offs) ebytes accdesc (Sail.BitVec.castWidth w__5))
                            (pure (rval))) ) : SailM (BitVec datasize) )
                      let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
                      let tt : Int := (fmod_int (tt +i 1) 32)
                      (pure ((offs, rval, tt)))
                  (pure loop_vars_2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec datasize) × Int) )
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))
  if (wback : Bool)
  then
    (do
      let offs ← (( do
        if ((m != 31) : Bool)
        then
          (do
            (X_read m 64))
        else (pure (offs)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set (address + offs)))
      else
        (do
          (X_set n 64 (address + offs))))
  else (pure (()))


end ArmFull.Functions
