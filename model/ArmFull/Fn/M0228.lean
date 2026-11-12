import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0052
import ArmFull.Fn.M0056
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0100
import ArmFull.Fn.M0118
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0148
import ArmFull.Fn.M0154
import ArmFull.Fn.M0157
import ArmFull.Fn.M0158
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0189
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0200
import ArmFull.Fn.M0202
import ArmFull.Fn.M0204
import ArmFull.Fn.M0209
import ArmFull.Fn.M0210
import ArmFull.Fn.M0212
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0218
import ArmFull.Fn.M0219

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

/-- Type quantifiers: pl : Int, vl : Int -/
def TakeTransactionCheckpoint (vl : Int) (pl : Int) : SailM Unit := do
  let w__0 ← (( do readReg TSTATE ) : SailM TMState )
  let w__1 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
  writeReg TSTATE { w__0 with SP := w__1 }
  let w__2 ← (( do readReg TSTATE ) : SailM TMState )
  let w__3 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg TSTATE { w__2 with ICC_PMR_EL1 := w__3 }
  let w__4 ← (( do readReg TSTATE ) : SailM TMState )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg TSTATE { w__4 with nzcv := (w__5.N +++ (w__6.Z +++ (w__7.C +++ w__8.V))) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  let split_vec := (w__9.D +++ (w__10.A +++ (w__11.I +++ w__12.F)))
  let w__13 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__13 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__14 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__14 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__15 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__15 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__16 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__16 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let loop_n_lower : Nat := 0
  let loop_n_upper : Nat := 30
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__17 ← (( do readReg TSTATE ) : SailM TMState )
        let w__18 ← (( do readReg TSTATE ) : SailM TMState )
        let w__19 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
        writeReg TSTATE { w__17 with X := (vectorUpdate w__18.X (Sail.Int.toNatChecked (n)) w__19) }
    (pure loop_vars))
  let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__21 ← (( do (IsFPEnabled w__20.EL) ) : SailM Bool )
  if (w__21 : Bool)
  then
    (do
      let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__23 ← (( do (IsSVEEnabled w__22.EL) ) : SailM Bool )
      if (w__23 : Bool)
      then
        (do
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 31
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert ((0 ≤b (vl -i 1)) && ((vl -i 1) <b 2048)) "sail-arm/v8_base.sail:33408.66-33408.67"
                let w__24 ← (( do readReg TSTATE ) : SailM TMState )
                let w__25 ← (( do readReg TSTATE ) : SailM TMState )
                let w__26 ← (( do readReg TSTATE ) : SailM TMState )
                let w__27 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Z_read n (Sail.Int.toNatChecked (vl)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (vl : Int))) )
                writeReg TSTATE { w__24 with Z := (vectorUpdate w__25.Z (Sail.Int.toNatChecked (n))
                    (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.updateSubrange
                      (GetElem?.getElem! w__26.Z (Sail.Int.toNatChecked (n)))
                      (Sail.Int.toNatChecked ((vl -i 1))) 0 (Sail.BitVec.castWidth w__27)))) }
            (pure loop_vars))
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 15
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert ((0 ≤b (pl -i 1)) && ((pl -i 1) <b 256)) "sail-arm/v8_base.sail:33412.65-33412.66"
                let w__28 ← (( do readReg TSTATE ) : SailM TMState )
                let w__29 ← (( do readReg TSTATE ) : SailM TMState )
                let w__30 ← (( do readReg TSTATE ) : SailM TMState )
                let w__31 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (P_read n (Sail.Int.toNatChecked (pl)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (pl : Int))) )
                writeReg TSTATE { w__28 with P := (vectorUpdate w__29.P (Sail.Int.toNatChecked (n))
                    (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.updateSubrange
                      (GetElem?.getElem! w__30.P (Sail.Int.toNatChecked (n)))
                      (Sail.Int.toNatChecked ((pl -i 1))) 0 (Sail.BitVec.castWidth w__31)))) }
            (pure loop_vars))
          ArmFull.assert ((0 ≤b (pl -i 1)) && ((pl -i 1) <b 256)) "sail-arm/v8_base.sail:33415.61-33415.62"
          let w__32 ← (( do readReg TSTATE ) : SailM TMState )
          let w__33 ← (( do readReg TSTATE ) : SailM TMState )
          let w__34 ← (( do ((Sail.BitVec.castWidth ) <$> (FFR_read (Sail.Int.toNatChecked (pl))))
            ) : SailM (BitVec (Sail.Int.toNatChecked (pl : Int))) )
          writeReg TSTATE { w__32 with FFR := (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.updateSubrange
              w__33.FFR (Sail.Int.toNatChecked ((pl -i 1))) 0 (Sail.BitVec.castWidth w__34))) })
      else
        (do
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 31
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__35 ← (( do readReg TSTATE ) : SailM TMState )
                let w__36 ← (( do readReg TSTATE ) : SailM TMState )
                let w__37 ← (( do readReg TSTATE ) : SailM TMState )
                let w__38 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
                writeReg TSTATE { w__35 with Z := (vectorUpdate w__36.Z (Sail.Int.toNatChecked (n))
                    (Sail.BitVec.updateSubrange
                      (GetElem?.getElem! w__37.Z (Sail.Int.toNatChecked (n))) 127 0 w__38)) }
            (pure loop_vars)))
      let w__39 ← (( do readReg TSTATE ) : SailM TMState )
      let w__40 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg TSTATE { w__39 with FPCR := w__40 }
      let w__41 ← (( do readReg TSTATE ) : SailM TMState )
      let w__42 ← (( do readReg FPSR ) : SailM (BitVec 64) )
      writeReg TSTATE { w__41 with FPSR := w__42 })
  else (pure (()))
  let w__43 ← (( do (HaveGCS ()) ) : SailM Bool )
  if (w__43 : Bool)
  then
    (do
      let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
      let questionMark := w__44.EL
      if ((questionMark == EL0) : Bool)
      then
        (do
          let w__45 ← (( do readReg TSTATE ) : SailM TMState )
          let w__46 ← (( do readReg GCSPR_EL0 ) : SailM (BitVec 64) )
          writeReg TSTATE { w__45 with GCSPR_ELx := w__46 })
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__47 ← (( do readReg TSTATE ) : SailM TMState )
              let w__48 ← (( do readReg GCSPR_EL1 ) : SailM (BitVec 64) )
              writeReg TSTATE { w__47 with GCSPR_ELx := w__48 })
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  let w__49 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__50 ← (( do readReg GCSPR_EL2 ) : SailM (BitVec 64) )
                  writeReg TSTATE { w__49 with GCSPR_ELx := w__50 })
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let w__51 ← (( do readReg TSTATE ) : SailM TMState )
                      let w__52 ← (( do readReg GCSPR_EL3 ) : SailM (BitVec 64) )
                      writeReg TSTATE { w__51 with GCSPR_ELx := w__52 })
                  else (pure (()))))))
  else (pure (()))


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset (cold : Bool) : SailM Unit := do
  let split_c0 ← (( (AArch64_AutoGen_ArchitectureReset__seg0 cold) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (AArch64_AutoGen_ArchitectureReset__seg1 cold) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (AArch64_AutoGen_ArchitectureReset__seg2 cold) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (AArch64_AutoGen_ArchitectureReset__seg3 cold) ) : SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (AArch64_AutoGen_ArchitectureReset__seg4 cold) ) : SailM Bool
                    )
                  if (split_c4 : Bool)
                  then (AArch64_AutoGen_ArchitectureReset__seg5 cold)
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


def SPEGetRandomInterval (_ : Unit) : SailM (BitVec 8) := do
  let new_byte ← (( do (undefined_bitvector_at (← occLabel 2430) 8) ) : SailM (BitVec 8) )
  let w__0 ← (( do readReg __SPE_LFSR_initialized ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      writeReg __SPE_LFSR_initialized true
      let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      writeReg __SPE_LFSR (Sail.BitVec.extractLsb w__1 23 0)
      let new_byte ← (( do
        let loop_i_lower : Nat := 0
        let loop_i_upper : Nat := 7
        (do
          let mut loop_vars := new_byte
          for i in [loop_i_upper:loop_i_lower:-1]i do
            let new_byte := loop_vars
            loop_vars ← do
              let w__2 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
              let w__3 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
              let w__4 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
              let new_byte :=
                (((Sail.BitVec.castWidth (m := 8) ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                      w__2 16 9)) ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__3
                      21 14)))) ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__4 22
                    15))) : (BitVec 8))
              let w__5 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
              let new_byte :=
                ((new_byte ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__5 23 16))) : (BitVec 8))
              let w__6 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
              writeReg __SPE_LFSR ((Sail.BitVec.extractLsb w__6 15 0) +++ new_byte)
              (pure (new_byte))
          (pure loop_vars)) ) : SailM (BitVec 8) )
      (pure (())))
  else
    (do
      let w__7 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
      let w__8 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
      let w__9 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
      let new_byte : (BitVec 8) :=
        (((Sail.BitVec.castWidth (m := 8) ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
              w__7 16 9)) ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__8 21 14)))) ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
            w__9 22 15))) : (BitVec 8))
      let w__10 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
      let new_byte : (BitVec 8) :=
        (new_byte ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__10 23 16)))
      let w__11 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
      writeReg __SPE_LFSR ((Sail.BitVec.extractLsb w__11 15 0) +++ new_byte))
  let w__12 ← (( do readReg __SPE_LFSR ) : SailM (BitVec 24) )
  (pure ((Sail.BitVec.extractLsb w__12 23 16)))


/-- Type quantifiers: k_branch_conditional : Bool -/
def BranchNotTaken (branchtype : BranchType) (branch_conditional : Bool) : SailM Unit := do
  let branchtaken : Bool := false
  let w__0 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      (SPEBranch w__1 branchtype branch_conditional branchtaken))
  else (pure (()))


def AArch64_RestrictPrediction (val_name : (BitVec 64)) (restriction : RestrictType) : SailM Unit := do
  let c ← (( do (undefined_ExecutionCntxt (← occLabel 2492) ()) ) : SailM ExecutionCntxt )
  let target_el : (BitVec 2) := (Sail.BitVec.extractLsb val_name 25 24)
  let w__1 ← (( do
    if (((! (HaveEL target_el)) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) >b (BitVec.toNat w__0.EL)) : Bool)))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let ns : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 26)]))
  let nse : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 27)]))
  let ss ← (( do (TargetSecurityState ns nse) ) : SailM SecurityState )
  if (((BEq.beq ss SS_Root) && (target_el != EL3)) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let w__4 ← (( do
    (pure ((← do
          (pure ((← do
                let w__2 ← (( do (HaveRME ()) ) : SailM Bool )
                (pure (((! w__2) : Bool)))) && ((target_el == EL3) : Bool)))) && ((bne ss SS_Secure) : Bool)))
    ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let c : ExecutionCntxt := { c with security := ss }
  let c : ExecutionCntxt := { c with target_el := target_el }
  let w__5 ← (( do (EL2Enabled ()) ) : SailM Bool )
  let c ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__10 ← (( do
          if ((← do
               if ((← do
                    let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__6.EL == EL0) : Bool)))) : Bool)
               then
                 (do
                   let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
                   (pure (((! w__7) : Bool))))
               else (pure false)) : Bool)
          then (pure true)
          else
            (do
              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__9.EL == EL1) : Bool)))) ) : SailM Bool )
        if (w__10 : Bool)
        then
          (do
            let c : ExecutionCntxt := { c with is_vmid_valid := true }
            let c : ExecutionCntxt := { c with all_vmid := false }
            let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
            let c := ({ c with vmid := w__11 } : ExecutionCntxt)
            (pure (c)))
        else
          (do
            let w__14 ← (( do
              (pure ((← do
                    if (((target_el == EL0) : Bool) : Bool)
                    then
                      (do
                        let w__12 ← (( do (ELIsInHost target_el) ) : SailM Bool )
                        (pure (((! w__12) : Bool))))
                    else (pure false)) || ((target_el == EL1) : Bool))) ) : SailM Bool )
            let c : ExecutionCntxt :=
              if (w__14 : Bool)
              then
                (let c : ExecutionCntxt := { c with is_vmid_valid := true }
                let c : ExecutionCntxt :=
                  { c with all_vmid := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 48)])) == 1#1) }
                { c with vmid := (Sail.BitVec.extractLsb val_name 47 32) })
              else { c with is_vmid_valid := false }
            (pure (c))))
    else
      (let c : ExecutionCntxt := { c with is_vmid_valid := false }
      (pure (c))) ) : SailM ExecutionCntxt )
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  let c ← (( do
    if ((w__15.EL == EL0) : Bool)
    then
      (do
        let c : ExecutionCntxt := { c with is_asid_valid := true }
        let c : ExecutionCntxt := { c with all_asid := false }
        let w__16 ← (( do (ASID_read ()) ) : SailM (BitVec 16) )
        let c := ({ c with asid := w__16 } : ExecutionCntxt)
        (pure (c)))
    else
      (let c : ExecutionCntxt :=
        if ((target_el == EL0) : Bool)
        then
          (let c : ExecutionCntxt := { c with is_asid_valid := true }
          let c : ExecutionCntxt :=
            { c with all_asid := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 16)])) == 1#1) }
          { c with asid := (Sail.BitVec.extractLsb val_name 15 0) })
        else { c with is_asid_valid := false }
      (pure (c))) ) : SailM ExecutionCntxt )
  let c : ExecutionCntxt := { c with restriction := restriction }
  (pure ((RESTRICT_PREDICTIONS c)))


def AArch32_S1TTWParamsEL10 (va : (BitVec 32)) : SailM S1TTWParams := do
  let mair ← (( do (undefined_bitvector_at (← occLabel 2497) 64) ) : SailM (BitVec 64) )
  let sif ← (( do (undefined_bitvector_at (← occLabel 2498) 1) ) : SailM (BitVec 1) )
  let ttbcr ← (( do (undefined_TTBCR_Type (← occLabel 2499) ()) ) : SailM TTBCR_Type )
  let ttbcr2 ← (( do (undefined_TTBCR2_Type (← occLabel 2500) ()) ) : SailM TTBCR2_Type )
  let sctlr ← (( do (undefined_SCTLR_Type (← occLabel 2501) ()) ) : SailM SCTLR_Type )
  let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  let (mair, sctlr, sif, ttbcr, ttbcr2) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (TTBCR_NS_read ()) ) : SailM (BitVec 32) )
        let ttbcr := (w__1 : (BitVec 32))
        let w__2 ← (( do (TTBCR2_NS_read ()) ) : SailM (BitVec 32) )
        let ttbcr2 := (w__2 : (BitVec 32))
        let w__3 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
        let sctlr := (w__3 : (BitVec 32))
        let w__4 ← (( do (MAIR1_NS_read ()) ) : SailM (BitVec 32) )
        let w__5 ← (( do (MAIR0_NS_read ()) ) : SailM (BitVec 32) )
        let mair := ((w__4 +++ w__5) : (BitVec 64))
        let w__6 ← (( do readReg SCR ) : SailM (BitVec 32) )
        let sif := ((_get_SCR_Type_SIF w__6) : (BitVec 1))
        (pure ((mair, sctlr, sif, ttbcr, ttbcr2))))
    else
      (do
        let w__7 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        let ttbcr := (w__7 : (BitVec 32))
        let w__8 ← (( do (TTBCR2_read ()) ) : SailM (BitVec 32) )
        let ttbcr2 := (w__8 : (BitVec 32))
        let w__9 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
        let sctlr := (w__9 : (BitVec 32))
        let w__10 ← (( do (MAIR1_read ()) ) : SailM (BitVec 32) )
        let w__11 ← (( do (MAIR0_read ()) ) : SailM (BitVec 32) )
        let mair := ((w__10 +++ w__11) : (BitVec 64))
        let w__13 ← (( do
          if ((HaveEL EL3) : Bool)
          then
            (do
              let w__12 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((_get_SCR_EL3_Type_SIF w__12))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let sif := (w__13 : (BitVec 1))
        (pure ((mair, sctlr, sif, ttbcr, ttbcr2)))) ) : SailM
    ((BitVec 64) × (BitVec 32) × (BitVec 1) × (BitVec 32) × (BitVec 32)) )
  ArmFull.assert ((_get_TTBCR_Type_EAE ttbcr) == 1#1) "sail-arm/v8_base.sail:37139.28-37139.29"
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 2502) ()) ) : SailM S1TTWParams )
  let walkparams : S1TTWParams := { walkparams with t0sz := (_get_TTBCR_Type_T0SZ ttbcr) }
  let walkparams : S1TTWParams := { walkparams with t1sz := (_get_TTBCR_Type_T1SZ ttbcr) }
  let walkparams : S1TTWParams := { walkparams with ee := (_get_SCTLR_Type_EE sctlr) }
  let walkparams : S1TTWParams := { walkparams with wxn := (_get_SCTLR_Type_WXN sctlr) }
  let walkparams : S1TTWParams := { walkparams with uwxn := (_get_SCTLR_Type_UWXN sctlr) }
  let w__14 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let w__15 : (BitVec 1) :=
    if (w__14 : Bool)
    then (_get_SCTLR_Type_nTLSMD sctlr)
    else 1#1
  let walkparams := ({ walkparams with ntlsmd := w__15 } : S1TTWParams)
  let walkparams : S1TTWParams := { walkparams with mair := (Mk_MAIRType mair) }
  let walkparams : S1TTWParams := { walkparams with sif := sif }
  let varange ← (( do (AArch32_GetVARange va walkparams.t0sz walkparams.t1sz) ) : SailM VARange )
  if ((BEq.beq varange VARange_LOWER) : Bool)
  then
    (do
      let walkparams : S1TTWParams := { walkparams with sh := (_get_TTBCR_Type_SH0 ttbcr) }
      let walkparams : S1TTWParams := { walkparams with irgn := (_get_TTBCR_Type_IRGN0 ttbcr) }
      let walkparams : S1TTWParams := { walkparams with orgn := (_get_TTBCR_Type_ORGN0 ttbcr) }
      let w__16 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
      let w__17 : (BitVec 1) :=
        if (w__16 : Bool)
        then ((_get_TTBCR_Type_T2E ttbcr) &&& (_get_TTBCR2_Type_HPD0 ttbcr2))
        else 0#1
      let walkparams := ({ walkparams with hpd := w__17 } : S1TTWParams)
      (pure (walkparams)))
  else
    (do
      let walkparams : S1TTWParams := { walkparams with sh := (_get_TTBCR_Type_SH1 ttbcr) }
      let walkparams : S1TTWParams := { walkparams with irgn := (_get_TTBCR_Type_IRGN1 ttbcr) }
      let walkparams : S1TTWParams := { walkparams with orgn := (_get_TTBCR_Type_ORGN1 ttbcr) }
      let w__18 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
      let w__19 : (BitVec 1) :=
        if (w__18 : Bool)
        then ((_get_TTBCR_Type_T2E ttbcr) &&& (_get_TTBCR2_Type_HPD1 ttbcr2))
        else 0#1
      let walkparams := ({ walkparams with hpd := w__19 } : S1TTWParams)
      (pure (walkparams)))


/-- Type quantifiers: size : Int -/
def AArch32_GetTranslationStartInfo (regime : Regime) (ss : SecurityState) (accdesc : AccessDescriptor) (va : (BitVec 32)) (size : Int) : SailM TranslationStartInfo := do
  let tlbcontext ← (( do (AArch32_GetS1TLBContext regime ss va) ) : SailM TLBContext )
  let tsi : TranslationStartInfo :=
    { ss := ss
      regime := regime
      vmid := tlbcontext.vmid
      asid := tlbcontext.asid
      va := (Sail.BitVec.zeroExtend va 64)
      cnp := tlbcontext.cnp
      accdesc := accdesc
      size := size }
  (pure (tsi))


/-- Type quantifiers: size : Int -/
def AArch32_CheckVectorCatch (fault_in : FaultRecord) (vaddress : (BitVec 32)) (size : Int) : SailM FaultRecord := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert w__1 "sail-arm/v8_base.sail:40616.51-40616.52"
  let fault : FaultRecord := fault_in
  let val_match ← (( do (AArch32_VCRMatch vaddress) ) : SailM Bool )
  let w__3 ← (( do
    if ((((size == 4) && (! val_match)) : Bool) : Bool)
    then
      (do
        (AArch32_VCRMatch (BitVec.addInt vaddress 2)))
    else (pure false) ) : SailM Bool )
  let val_match ← (( do
    if (w__3 : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_VCMATCHHALF))
    else (pure (val_match)) ) : SailM Bool )
  let fault : FaultRecord :=
    if (val_match : Bool)
    then
      (let fault : FaultRecord := { fault with statuscode := Fault_Debug }
      { fault with debugmoe := DebugException_VectorCatch })
    else fault
  (pure (fault))


def AArch32_RestrictPrediction (val_name : (BitVec 32)) (restriction : RestrictType) : SailM Unit := do
  let c ← (( do (undefined_ExecutionCntxt (← occLabel 2694) ()) ) : SailM ExecutionCntxt )
  let target_el : (BitVec 2) := (Sail.BitVec.extractLsb val_name 25 24)
  let w__1 ← (( do
    if (((! (HaveEL target_el)) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) >b (BitVec.toNat w__0.EL)) : Bool)))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let ns : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 26)]))
  let nse ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
  let ss ← (( do (TargetSecurityState ns nse) ) : SailM SecurityState )
  let c : ExecutionCntxt := { c with security := ss }
  let c : ExecutionCntxt := { c with target_el := target_el }
  let w__2 ← (( do (EL2Enabled ()) ) : SailM Bool )
  let c ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__5 ← (( do
          if ((← do
               let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__3.EL == EL0) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__4.EL == EL1) : Bool)))) ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let c : ExecutionCntxt := { c with is_vmid_valid := true }
            let c : ExecutionCntxt := { c with all_vmid := false }
            let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
            let c := ({ c with vmid := w__6 } : ExecutionCntxt)
            (pure (c)))
        else
          (let c : ExecutionCntxt :=
            if (((target_el == EL0) || (target_el == EL1)) : Bool)
            then
              (let c : ExecutionCntxt := { c with is_vmid_valid := true }
              let c : ExecutionCntxt :=
                { c with all_vmid := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 27)])) == 1#1) }
              { c with vmid := (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb val_name 23 16) 16) })
            else { c with is_vmid_valid := false }
          (pure (c))))
    else
      (let c : ExecutionCntxt := { c with is_vmid_valid := false }
      (pure (c))) ) : SailM ExecutionCntxt )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  let c ← (( do
    if ((w__7.EL == EL0) : Bool)
    then
      (do
        let c : ExecutionCntxt := { c with is_asid_valid := true }
        let c : ExecutionCntxt := { c with all_asid := false }
        let w__8 ← (( do (ASID_read ()) ) : SailM (BitVec 16) )
        let c := ({ c with asid := w__8 } : ExecutionCntxt)
        (pure (c)))
    else
      (let c : ExecutionCntxt :=
        if ((target_el == EL0) : Bool)
        then
          (let c : ExecutionCntxt := { c with is_asid_valid := true }
          let c : ExecutionCntxt :=
            { c with all_asid := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access val_name 8)])) == 1#1) }
          { c with asid := (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb val_name 7 0) 16) })
        else { c with is_asid_valid := false }
      (pure (c))) ) : SailM ExecutionCntxt )
  let c : ExecutionCntxt := { c with restriction := restriction }
  (pure ((RESTRICT_PREDICTIONS c)))


/-- Type quantifiers: n : Int -/
def S_set (n : Int) (value_name : (BitVec 32)) : SailM Unit := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:42219.27-42219.28"
  let base : Nat := (Sail.Int.toNatChecked (((Nat.mod (Sail.Int.toNatChecked (n)) 4) *i 32)))
  let vreg ← (( do (V_read (Int.ediv (Sail.Int.toNatChecked (n)) 4) 128) ) : SailM (BitVec 128) )
  let vreg : (BitVec 128) :=
    (Sail.BitVec.updateSubrange vreg (Sail.Int.toNatChecked ((base +i 31))) base
      (Sail.BitVec.castWidth value_name))
  (V_set (Int.ediv (Sail.Int.toNatChecked (n)) 4) 128 vreg)


/-- Type quantifiers: n : Int -/
def D_set (n : Int) (value_name : (BitVec 64)) : SailM Unit := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:42230.27-42230.28"
  let base : Nat := (Sail.Int.toNatChecked (((Nat.mod (Sail.Int.toNatChecked (n)) 2) *i 64)))
  let vreg ← (( do (V_read (Int.ediv (Sail.Int.toNatChecked (n)) 2) 128) ) : SailM (BitVec 128) )
  let vreg : (BitVec 128) :=
    (Sail.BitVec.updateSubrange vreg (Sail.Int.toNatChecked ((base +i 63))) base
      (Sail.BitVec.castWidth value_name))
  (V_set (Int.ediv (Sail.Int.toNatChecked (n)) 2) 128 vreg)


/-- Type quantifiers: n : Int -/
def Q_set (n : Int) (value_name : (BitVec 128)) : SailM Unit := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 15)) "sail-arm/v8_base.sail:42248.27-42248.28"
  (V_set n 128 value_name)


def PCStoreValue (_ : Unit) : SailM (BitVec 32) := do
  (PC_read__1 ())


def AArch32_ESBOperation (_ : Unit) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2770) 2) ) : SailM (BitVec 2) )
  let route_to_aarch64 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__5 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__5 : Bool)
    then
      (do
        if ((← do
             let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_AMO w__7) == 1#1) : Bool)))))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__10 ← (( do
    if ((((! route_to_aarch64) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__9 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__9) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__10 : Bool)
    then
      (do
        let w__11 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
        let route_to_aarch64 := ((w__11 == 1#1) : Bool)
        (pure (route_to_aarch64)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if (route_to_aarch64 : Bool)
  then
    (do
      (AArch64_ESBOperation ()))
  else
    (do
      let route_to_monitor ← (( do
        if ((← do
             if (((HaveEL EL3) : Bool) : Bool)
             then
               (do
                 (ELUsingAArch32 EL3))
             else (pure false)) : Bool)
        then
          (do
            let w__14 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            (pure (((w__14 == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let route_to_hyp ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__15.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__16.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            if ((← do
                 let w__20 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                 (pure ((((_get_HCR_Type_TGE w__20) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__21 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_AMO w__21) == 1#1) : Bool)))))
        else (pure false) ) : SailM Bool )
      let target ← (( do (undefined_bitvector_at (← occLabel 2771) 5) ) : SailM (BitVec 5) )
      let target ← (( do
        if (route_to_monitor : Bool)
        then (pure (M32_Monitor))
        else
          (do
            let w__24 ← (( do
              if (route_to_hyp : Bool)
              then (pure true)
              else
                (do
                  let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__23.M == M32_Hyp) : Bool)))) ) : SailM Bool )
            let target : (BitVec 5) :=
              if (w__24 : Bool)
              then M32_Hyp
              else M32_Abort
            (pure (target))) ) : SailM (BitVec 5) )
      let mask_active ← (( do (undefined_bool_at (← occLabel 2772) ()) ) : SailM Bool )
      let w__25 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      let mask_active ← (( do
        if ((BEq.beq w__25 SS_Secure) : Bool)
        then (pure (true))
        else
          (do
            if ((target == M32_Monitor) : Bool)
            then
              (do
                if ((← do
                     let w__26 ← (( do readReg SCR ) : SailM (BitVec 32) )
                     (pure ((((_get_SCR_Type_AW w__26) == 1#1) : Bool)))) : Bool)
                then
                  (do
                    if (((! (HaveEL EL2)) : Bool) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((← do
                             let w__27 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                             (pure ((((_get_HCR_Type_TGE w__27) == 0#1) : Bool)))) : Bool)
                        then
                          (do
                            let w__28 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_HCR_Type_AMO w__28) == 0#1) : Bool))))
                        else (pure false)))
                else (pure false))
            else
              (do
                if (((target == M32_Abort) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__32.M == M32_Hyp) : Bool)))))) ) : SailM Bool )
      let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
      let mask_set : Bool := (w__34.A == 1#1)
      let (_, __tup_1) ← (( do (ELFromM32 target) ) : SailM (Bool × (BitVec 2)) )
      let el : (BitVec 2) := __tup_1
      let intdis ← (( do
        if ((← do
             (Halted ())) : Bool)
        then (pure true)
        else
          (do
            (ExternalDebugInterruptsDisabled el)) ) : SailM Bool )
      let masked : Bool := (intdis || (mask_active && mask_set))
      let w__38 ← (( do
        if (masked : Bool)
        then
          (do
            (IsSynchronizablePhysicalSErrorPending ()))
        else (pure false) ) : SailM Bool )
      if (w__38 : Bool)
      then
        (do
          let syndrome : (BitVec 32) := (Zeros (n := 32))
          let syndrome : (BitVec 32) := (BitVec.update syndrome 31 (Bit 1#1))
          let w__39 ← (( do (AArch32_PhysicalSErrorSyndrome ()) ) : SailM (BitVec 16) )
          let syndrome := ((Sail.BitVec.updateSubrange syndrome 15 0 w__39) : (BitVec 32))
          (DISR_write (Mk_DISR_Type syndrome))
          (pure ((ClearPendingPhysicalSError ()))))
      else (pure (())))


end ArmFull.Functions
