import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0143
import ArmFull.Fn.M0151
import ArmFull.Fn.M0164
import ArmFull.Fn.M0165
import ArmFull.Fn.M0202
import ArmFull.Fn.M0240
import ArmFull.Fn.M0243
import ArmFull.Fn.M0244
import ArmFull.Fn.M0245
import ArmFull.Fn.M0246
import ArmFull.Fn.M0247
import ArmFull.Fn.M0248
import ArmFull.Fn.M0581
import ArmFull.Fn.M0839
import ArmFull.Fn.M0840
import ArmFull.Fn.M0843
import ArmFull.Fn.M0850
import ArmFull.Fn.M0851
import ArmFull.Fn.M0853
import ArmFull.Fn.M0854
import ArmFull.Fn.M0855
import ArmFull.Fn.M0929
import ArmFull.Fn.M0930
import ArmFull.Fn.M0931
import ArmFull.Fn.M0932
import ArmFull.Fn.M0937
import ArmFull.Fn.M1274
import ArmFull.Fn.M1275
import ArmFull.Fn.M1276
import ArmFull.Fn.M1277
import ArmFull.Fn.M1349
import ArmFull.Fn.M1350
import ArmFull.Fn.M1406
import ArmFull.Fn.M1407
import ArmFull.Fn.M1442
import ArmFull.Fn.M1443
import ArmFull.Fn.M1444
import ArmFull.Fn.M1445
import ArmFull.Fn.M1446
import ArmFull.Fn.M1447
import ArmFull.Fn.M1448
import ArmFull.Fn.M1468
import ArmFull.Fn.M1469
import ArmFull.Fn.M1470
import ArmFull.Fn.M1471
import ArmFull.Fn.M1472
import ArmFull.Fn.M1473

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

/-- Type quantifiers: k_read : Bool, sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem sys_op0 [2, 3] ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_register_system (read : Bool) (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) : SailM Unit := do
  if (read : Bool)
  then
    (do
      (AArch64_SysRegRead sys_op0 sys_op1 sys_crn sys_crm sys_op2 t))
  else
    (do
      (AArch64_SysRegWrite sys_op0 sys_op1 sys_crn sys_crm sys_op2 t))


def decode_sys_aarch64_instrs_system_sysops (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess 0b01#2 op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let sys_op0 : Nat := 1
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  let has_result : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_sysops has_result (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) sys_op0 (Sail.Int.toNatChecked (sys_op1))
    (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t)))


def decode_sysl_aarch64_instrs_system_sysops (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess 0b01#2 op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let sys_op0 : Nat := 1
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  let has_result : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_sysops has_result (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) sys_op0 (Sail.Int.toNatChecked (sys_op1))
    (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t)))


/-- Type quantifiers: pc : Int -/
def __DecodeT32 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let split_c0 ← (( (__DecodeT32__seg0 pc __opcode) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (__DecodeT32__seg1 pc __opcode) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (__DecodeT32__seg2 pc __opcode) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (__DecodeT32__seg3 pc __opcode) ) : SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (__DecodeT32__seg4 pc __opcode) ) : SailM Bool )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← (( (__DecodeT32__seg5 pc __opcode) ) : SailM Bool )
                      if (split_c5 : Bool)
                      then
                        (do
                          let split_c6 ← (( (__DecodeT32__seg6 pc __opcode) ) : SailM Bool )
                          if (split_c6 : Bool)
                          then
                            (do
                              let split_c7 ← (( (__DecodeT32__seg7 pc __opcode) ) : SailM Bool )
                              if (split_c7 : Bool)
                              then
                                (do
                                  let split_c8 ← (( (__DecodeT32__seg8 pc __opcode) ) : SailM Bool
                                    )
                                  if (split_c8 : Bool)
                                  then
                                    (do
                                      let split_c9 ← (( (__DecodeT32__seg9 pc __opcode) ) : SailM
                                        Bool )
                                      if (split_c9 : Bool)
                                      then
                                        (do
                                          let split_c10 ← (( (__DecodeT32__seg10 pc __opcode) ) :
                                            SailM Bool )
                                          if (split_c10 : Bool)
                                          then
                                            (do
                                              let split_c11 ← (( (__DecodeT32__seg11 pc __opcode)
                                                ) : SailM Bool )
                                              if (split_c11 : Bool)
                                              then
                                                (do
                                                  let split_c12 ← ((
                                                    (__DecodeT32__seg12 pc __opcode) ) : SailM Bool
                                                    )
                                                  if (split_c12 : Bool)
                                                  then
                                                    (do
                                                      let split_c13 ← ((
                                                        (__DecodeT32__seg13 pc __opcode) ) : SailM
                                                        Bool )
                                                      if (split_c13 : Bool)
                                                      then (__DecodeT32__seg14 pc __opcode)
                                                      else (pure ()))
                                                  else (pure ()))
                                              else (pure ()))
                                          else (pure ()))
                                      else (pure ()))
                                  else (pure ()))
                              else (pure ()))
                          else (pure ()))
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: pc : Int -/
def __DecodeA32 (pc : Int) (opcode : (BitVec 32)) : SailM Unit := do
  let v__28 := opcode
  if (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb v__28 31 27)) == (0b11110#5 : (BitVec 5))) : Bool)
  then
    (do
      (__DecodeA32_Unconditional pc opcode))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb v__28 27 26)) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          (__DecodeA32_DataProMisc pc opcode))
      else
        (do
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb v__28 27 25)) == (0b010#3 : (BitVec 3))) : Bool)
          then
            (do
              (__DecodeA32_LoadStoreImmLit pc opcode))
          else
            (do
              if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb v__28 27 25)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       v__28 4 4)) == (0#1 : (BitVec 1)))) : Bool)
              then
                (do
                  (__DecodeA32_LoadStoreReg pc opcode))
              else
                (do
                  if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb v__28 27 25)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           v__28 4 4)) == (1#1 : (BitVec 1)))) : Bool)
                  then
                    (do
                      (__DecodeA32_Media pc opcode))
                  else
                    (do
                      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb v__28 27 26)) == (0b10#2 : (BitVec 2))) : Bool)
                      then
                        (do
                          (__DecodeA32_BranchBlock pc opcode))
                      else
                        (do
                          (__DecodeA32_SysASIMDFP pc opcode)))))))


def decode_mrs_aarch64_instrs_system_register_system (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let sys_op0 : Int := (2 +i (BitVec.toNat o0))
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system read (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) (Sail.Int.toNatChecked (sys_op0))
    (Sail.Int.toNatChecked (sys_op1)) (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t)))


def decode_msr_reg_aarch64_instrs_system_register_system (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let sys_op0 : Int := (2 +i (BitVec.toNat o0))
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system read (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) (Sail.Int.toNatChecked (sys_op0))
    (Sail.Int.toNatChecked (sys_op1)) (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t)))


def ExecuteA32 (instr : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg _PC ) : SailM (BitVec 64) )
  (__DecodeA32 (BitVec.toNat w__0) instr)


def ExecuteT32__1 (instr : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      sailTryCatch ((do
          let w__1 ← (( do (__DefaultCond __T32) ) : SailM (BitVec 4) )
          (__SetThisInstrDetails __T32 instr w__1)
          let w__2 ← (( do readReg _PC ) : SailM (BitVec 64) )
          (__DecodeT32 (BitVec.toNat w__2) instr))) (fun the_exception => 
        match the_exception with
          | exn =>
            (do
              if ((IsExceptionTaken exn) : Bool)
              then (pure (()))
              else
                (do
                  if ((((IsSEE exn) || (IsUNDEFINED exn)) || (IsUNPREDICTABLE exn)) : Bool)
                  then
                    (do
                      (UnallocatedT32_32_Instruction instr))
                  else sailThrow (exn)))))
  else
    (do
      let w__3 ← (( do readReg _PC ) : SailM (BitVec 64) )
      (__DecodeT32 (BitVec.toNat w__3) instr))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_BranchExcSys (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1 ← (( do
    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 8 6)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
               __opcode 4 0)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 63) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 63
      let op2 := (BitVec.slice __opcode 5 3)
      let CRm := (BitVec.slice __opcode 8 4)
      (decode_autia_aarch64_instrs_integer_pac_autia_hint op2 CRm))
  else
    (do
      let w__3 ← (( do
        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 8 6)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 4 0)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 65) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 65
          let op2 := (BitVec.slice __opcode 5 3)
          let CRm := (BitVec.slice __opcode 8 4)
          (decode_autib_aarch64_instrs_integer_pac_autib_hint op2 CRm))
      else
        (do
          let w__5 ← (( do
            if (((__opcode == 0b11010101000000000100000001011111#32) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 66) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 66
              let CRm := (BitVec.slice __opcode 8 4)
              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 11)])) != 0#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_axflag_aarch64_instrs_integer_flags_axflag CRm)))
          else
            (do
              let w__7 ← (( do
                if ((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 31 26)) == (0b000101#6 : (BitVec 6))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 67) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 67
                  let imm26 := (BitVec.slice __opcode 0 26)
                  let op := (BitVec.slice __opcode 31 1)
                  (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op))
              else
                (do
                  let w__9 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 31 26)) == (0b100101#6 : (BitVec 6))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 68) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 68
                      let imm26 := (BitVec.slice __opcode 0 26)
                      let op := (BitVec.slice __opcode 31 1)
                      (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x54#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 69) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 69
                          let cond := (BitVec.slice __opcode 0 4)
                          let imm19 := (BitVec.slice __opcode 5 19)
                          (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x54#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 4 4)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 70) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 70
                              let cond := (BitVec.slice __opcode 0 4)
                              let imm19 := (BitVec.slice __opcode 5 19)
                              (decode_bc_cond_aarch64_instrs_branch_conditional_hinted cond imm19))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                         __opcode 31 10)) == (0b1101011000111111000000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                         __opcode 4 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 90) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 90
                                  let Rm := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let M := (BitVec.slice __opcode 10 1)
                                  let A := (BitVec.slice __opcode 11 1)
                                  let op := (BitVec.slice __opcode 21 2)
                                  let Z := (BitVec.slice __opcode 24 1)
                                  (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A
                                    op Z))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                             __opcode 31 25)) == (0b1101011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                             __opcode 23 11)) == (0b0011111100001#13 : (BitVec 13)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 91) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 91
                                      let Rm := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let M := (BitVec.slice __opcode 10 1)
                                      let A := (BitVec.slice __opcode 11 1)
                                      let op := (BitVec.slice __opcode 21 2)
                                      let Z := (BitVec.slice __opcode 24 1)
                                      (decode_blra_aarch64_instrs_branch_unconditional_register Rm
                                        Rn M A op Z))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                 __opcode 31 10)) == (0b1101011000011111000000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                 __opcode 4 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 92) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 92
                                          let Rm := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let M := (BitVec.slice __opcode 10 1)
                                          let A := (BitVec.slice __opcode 11 1)
                                          let op := (BitVec.slice __opcode 21 2)
                                          let Z := (BitVec.slice __opcode 24 1)
                                          (decode_br_aarch64_instrs_branch_unconditional_register Rm
                                            Rn M A op Z))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                     __opcode 31 25)) == (0b1101011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                     __opcode 23 11)) == (0b0001111100001#13 : (BitVec 13)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 93) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 93
                                              let Rm := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let M := (BitVec.slice __opcode 10 1)
                                              let A := (BitVec.slice __opcode 11 1)
                                              let op := (BitVec.slice __opcode 21 2)
                                              let Z := (BitVec.slice __opcode 24 1)
                                              (decode_bra_aarch64_instrs_branch_unconditional_register
                                                Rm Rn M A op Z))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                         __opcode 31 10)) == (0b1101011001011111000000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                         __opcode 4 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 94) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 94
                                                  let Rm := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let M := (BitVec.slice __opcode 10 1)
                                                  let A := (BitVec.slice __opcode 11 1)
                                                  let op := (BitVec.slice __opcode 21 2)
                                                  let Z := (BitVec.slice __opcode 24 1)
                                                  (decode_ret_aarch64_instrs_branch_unconditional_register
                                                    Rm Rn M A op Z))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                             __opcode 31 11)) == (0b110101100101111100001#21 : (BitVec 21))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                             __opcode 9 0)) == (0b1111111111#10 : (BitVec 10)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 95) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 95
                                                      let Rm := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let M := (BitVec.slice __opcode 10 1)
                                                      let A := (BitVec.slice __opcode 11 1)
                                                      let op := (BitVec.slice __opcode 21 2)
                                                      let Z := (BitVec.slice __opcode 24 1)
                                                      (decode_reta_aarch64_instrs_branch_unconditional_register
                                                        Rm Rn M A op Z))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b11010100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                 __opcode 4 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 96) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 96
                                                          let imm16 := (BitVec.slice __opcode 5 16)
                                                          (decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint
                                                            imm16))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb
                                                                     __opcode 31 8)) == (0xD50324#24 : (BitVec 24))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 5 0)) == (0b011111#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 97) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 97
                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                              (decode_bti_aarch64_instrs_system_hints
                                                                op2 CRm))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if (((__opcode == 0b11010101000000110010010100011111#32) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 98) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 98
                                                                  let op2 :=
                                                                    (BitVec.slice __opcode 5 3)
                                                                  let CRm :=
                                                                    (BitVec.slice __opcode 8 4)
                                                                  (decode_chkfeat_aarch64_instrs_system_hints
                                                                    op2 CRm))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if (((__opcode == 0b11010101000000110010001011011111#32) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 99) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 99
                                                                      let op2 :=
                                                                        (BitVec.slice __opcode 5 3)
                                                                      let CRm :=
                                                                        (BitVec.slice __opcode 8 4)
                                                                      (decode_clrbhb_aarch64_instrs_system_hints
                                                                        op2 CRm))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if (((__opcode == 0b11010101000000110010001010011111#32) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 100) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 100
                                                                          let op2 :=
                                                                            (BitVec.slice __opcode 5
                                                                              3)
                                                                          let CRm :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          (decode_csdb_aarch64_instrs_system_hints
                                                                            op2 CRm))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if (((__opcode == 0b11010101000000110010000011011111#32) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 101) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 101
                                                                              let op2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 3)
                                                                              let CRm :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 4)
                                                                              (decode_dgh_aarch64_instrs_system_hints
                                                                                op2 CRm))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if (((__opcode == 0b11010101000000110010001000011111#32) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 102) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 102
                                                                                  let op2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 3)
                                                                                  let CRm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  (decode_esb_aarch64_instrs_system_hints
                                                                                    op2 CRm))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if (((__opcode == 0b11010101000000110010001001111111#32) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 103) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 103
                                                                                      let op2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          3)
                                                                                      let CRm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          4)
                                                                                      (decode_gcsb_aarch64_instrs_system_hints
                                                                                        op2 CRm))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 12)) == (0xD5032#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 0)) == (0b11111#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 104) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 104
                                                                                          let op2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 3)
                                                                                          let CRm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          (decode_hint_aarch64_instrs_system_hints
                                                                                            op2 CRm))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if (((__opcode == 0b11010101000000110010000000011111#32) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 105) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 105
                                                                                              let op2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  3)
                                                                                              let CRm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  4)
                                                                                              (decode_nop_aarch64_instrs_system_hints
                                                                                                op2
                                                                                                CRm))
                                                                                          else
                                                                                            (do
                                                                                              let w__47 ← (( do
                                                                                                if (((__opcode == 0b11010101000000110010001000111111#32) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__46 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__46 <b 106) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__47 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 106
                                                                                                  let op2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      3)
                                                                                                  let CRm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  (decode_psb_aarch64_instrs_system_hints
                                                                                                    op2
                                                                                                    CRm))
                                                                                              else
                                                                                                (do
                                                                                                  let w__49 ← (( do
                                                                                                    if (((__opcode == 0b11010101000000110010000010011111#32) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__48 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__48 <b 107) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__49 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 107
                                                                                                      let op2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          3)
                                                                                                      let CRm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          4)
                                                                                                      (decode_sev_aarch64_instrs_system_hints
                                                                                                        op2
                                                                                                        CRm))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__51 ← (( do
                                                                                                        if (((__opcode == 0b11010101000000110010000010111111#32) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__50 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__50 <b 108) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__51 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 108
                                                                                                          let op2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              3)
                                                                                                          let CRm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          (decode_sevl_aarch64_instrs_system_hints
                                                                                                            op2
                                                                                                            CRm))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__53 ← (( do
                                                                                                            if (((__opcode == 0b11010101000000110010001001011111#32) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__52 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__52 <b 109) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__53 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 109
                                                                                                              let op2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  3)
                                                                                                              let CRm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              (decode_tsb_aarch64_instrs_system_hints
                                                                                                                op2
                                                                                                                CRm))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__55 ← (( do
                                                                                                                if (((__opcode == 0b11010101000000110010000001011111#32) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__54 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__54 <b 110) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__55 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 110
                                                                                                                  let op2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      3)
                                                                                                                  let CRm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      4)
                                                                                                                  (decode_wfe_aarch64_instrs_system_hints
                                                                                                                    op2
                                                                                                                    CRm))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__57 ← (( do
                                                                                                                    if (((__opcode == 0b11010101000000110010000001111111#32) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__56 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__56 <b 111) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__57 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 111
                                                                                                                      let op2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          3)
                                                                                                                      let CRm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          8
                                                                                                                          4)
                                                                                                                      (decode_wfi_aarch64_instrs_system_hints
                                                                                                                        op2
                                                                                                                        CRm))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__59 ← (( do
                                                                                                                        if (((__opcode == 0b11010101000000110010000000111111#32) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__58 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__58 <b 112) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__59 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 112
                                                                                                                          let op2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              3)
                                                                                                                          let CRm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              4)
                                                                                                                          (decode_yield_aarch64_instrs_system_hints
                                                                                                                            op2
                                                                                                                            CRm))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__61 ← (( do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   30
                                                                                                                                   24)) == (0b0110101#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__60 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__60 <b 117) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__61 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 117
                                                                                                                              let Rt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              let imm19 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  19)
                                                                                                                              let op :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  24
                                                                                                                                  1)
                                                                                                                              let sf :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  31
                                                                                                                                  1)
                                                                                                                              (decode_cbnz_aarch64_instrs_branch_conditional_compare
                                                                                                                                Rt
                                                                                                                                imm19
                                                                                                                                op
                                                                                                                                sf))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__63 ← (( do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       30
                                                                                                                                       24)) == (0b0110100#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__62 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__62 <b 118) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__63 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 118
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  let imm19 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      19)
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      24
                                                                                                                                      1)
                                                                                                                                  let sf :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      31
                                                                                                                                      1)
                                                                                                                                  (decode_cbz_aarch64_instrs_branch_conditional_compare
                                                                                                                                    Rt
                                                                                                                                    imm19
                                                                                                                                    op
                                                                                                                                    sf))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__65 ← (( do
                                                                                                                                    if (((__opcode == 0b11010101000000000100000000011111#32) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__64 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__64 <b 123) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__65 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 123
                                                                                                                                      let CRm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          8
                                                                                                                                          4)
                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 11)])) != 0#1)) : Bool)
                                                                                                                                      then
                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                          ()))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          (decode_cfinv_aarch64_instrs_integer_flags_cfinv
                                                                                                                                            CRm)))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__67 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 12)) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 7
                                                                                                                                                 0)) == (0x5F#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__66 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__66 <b 124) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__67 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 124
                                                                                                                                          let CRm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              4)
                                                                                                                                          (pure ((decode_clrex_aarch64_instrs_system_monitors
                                                                                                                                              CRm))))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__69 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b11010100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     0)) == (0b00001#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__68 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__68 <b 192) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__69 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 192
                                                                                                                                              let LL :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  2)
                                                                                                                                              let imm16 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  16)
                                                                                                                                              (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception
                                                                                                                                                LL
                                                                                                                                                imm16))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__71 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b11010100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         4
                                                                                                                                                         0)) == (0b00010#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__70 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__70 <b 193) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__71 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 193
                                                                                                                                                  let LL :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      2)
                                                                                                                                                  let imm16 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      16)
                                                                                                                                                  (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception
                                                                                                                                                    LL
                                                                                                                                                    imm16))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__73 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b11010100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             4
                                                                                                                                                             0)) == (0b00011#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__72 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__72 <b 194) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__73 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 194
                                                                                                                                                      let LL :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          2)
                                                                                                                                                      let imm16 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          16)
                                                                                                                                                      (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception
                                                                                                                                                        LL
                                                                                                                                                        imm16))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__75 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 12)) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 7
                                                                                                                                                                 0)) == (0xBF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__74 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__74 <b 195) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__75 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 195
                                                                                                                                                          let opc :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              2)
                                                                                                                                                          let CRm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              8
                                                                                                                                                              4)
                                                                                                                                                          (decode_dmb_aarch64_instrs_system_barriers_dmb
                                                                                                                                                            opc
                                                                                                                                                            CRm))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__77 ← (( do
                                                                                                                                                            if (((__opcode == 0b11010110101111110000001111100000#32) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__76 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__76 <b 196) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__77 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 196
                                                                                                                                                              (decode_drps_aarch64_instrs_branch_unconditional_dret
                                                                                                                                                                ()))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__79 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         12)) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         7
                                                                                                                                                                         0)) == (0x9F#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__78 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__78 <b 197) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__79 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 197
                                                                                                                                                                  let opc :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      2)
                                                                                                                                                                  let CRm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      8
                                                                                                                                                                      4)
                                                                                                                                                                  (decode_dsb_aarch64_instrs_system_barriers_dsb
                                                                                                                                                                    opc
                                                                                                                                                                    CRm))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__81 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             12)) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             9
                                                                                                                                                                             0)) == (0b1000111111#10 : (BitVec 10)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__80 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__80 <b 198) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__81 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 198
                                                                                                                                                                      let imm2 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          2)
                                                                                                                                                                      (decode_dsb_aarch64_instrs_system_barriers_dsb_nxs
                                                                                                                                                                        imm2))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__83 ← (( do
                                                                                                                                                                        if (((__opcode == 0b11010110100111110000001111100000#32) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__82 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__82 <b 203) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__83 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 203
                                                                                                                                                                          let op4 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              5)
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              5)
                                                                                                                                                                          let M :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              1)
                                                                                                                                                                          let A :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              11
                                                                                                                                                                              1)
                                                                                                                                                                          (decode_eret_aarch64_instrs_branch_unconditional_eret
                                                                                                                                                                            op4
                                                                                                                                                                            Rn
                                                                                                                                                                            M
                                                                                                                                                                            A))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__85 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     11)) == (0b110101101001111100001#21 : (BitVec 21))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     9
                                                                                                                                                                                     0)) == (0b1111111111#10 : (BitVec 10)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__84 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__84 <b 204) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__85 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 204
                                                                                                                                                                              let op4 :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  5)
                                                                                                                                                                              let Rn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  5
                                                                                                                                                                                  5)
                                                                                                                                                                              let M :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  10
                                                                                                                                                                                  1)
                                                                                                                                                                              let A :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  11
                                                                                                                                                                                  1)
                                                                                                                                                                              (decode_ereta_aarch64_instrs_branch_unconditional_eret
                                                                                                                                                                                op4
                                                                                                                                                                                Rn
                                                                                                                                                                                M
                                                                                                                                                                                A))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__87 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         21)) == (0b11010100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         4
                                                                                                                                                                                         0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__86 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__86 <b 478) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__87 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 478
                                                                                                                                                                                  let imm16 :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      16)
                                                                                                                                                                                  (decode_hlt_aarch64_instrs_system_exceptions_debug_halt
                                                                                                                                                                                    imm16))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__89 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             21)) == (0b11010100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             4
                                                                                                                                                                                             0)) == (0b00010#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__88 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__88 <b 479) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__89 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 479
                                                                                                                                                                                      let imm16 :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          5
                                                                                                                                                                                          16)
                                                                                                                                                                                      (decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc
                                                                                                                                                                                        imm16))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__91 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 31
                                                                                                                                                                                                 12)) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 7
                                                                                                                                                                                                 0)) == (0xDF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__90 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__90 <b 483) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__91 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 483
                                                                                                                                                                                          let opc :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              5
                                                                                                                                                                                              2)
                                                                                                                                                                                          let CRm :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              8
                                                                                                                                                                                              4)
                                                                                                                                                                                          (decode_isb_aarch64_instrs_system_barriers_isb
                                                                                                                                                                                            opc
                                                                                                                                                                                            CRm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__93 ← (( do
                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   31
                                                                                                                                                                                                   20)) == (0xD57#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__92 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__92 <b 699) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__93 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 699
                                                                                                                                                                                              let Rt :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  0
                                                                                                                                                                                                  5)
                                                                                                                                                                                              let op2 :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  5
                                                                                                                                                                                                  3)
                                                                                                                                                                                              let CRm :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  8
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let CRn :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  12
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let op1 :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  16
                                                                                                                                                                                                  3)
                                                                                                                                                                                              let o0 :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  19
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let L :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  21
                                                                                                                                                                                                  1)
                                                                                                                                                                                              (decode_mrrs_aarch64_instrs_system_register_system_128
                                                                                                                                                                                                Rt
                                                                                                                                                                                                op2
                                                                                                                                                                                                CRm
                                                                                                                                                                                                CRn
                                                                                                                                                                                                op1
                                                                                                                                                                                                o0
                                                                                                                                                                                                L))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__95 ← (( do
                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       31
                                                                                                                                                                                                       20)) == (0xD55#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__94 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__94 <b 700) : Bool))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                )
                                                                                                                                                                                                :
                                                                                                                                                                                                SailM
                                                                                                                                                                                                Bool
                                                                                                                                                                                                )
                                                                                                                                                                                              if (w__95 : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 700
                                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      0
                                                                                                                                                                                                      5)
                                                                                                                                                                                                  let op2 :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      5
                                                                                                                                                                                                      3)
                                                                                                                                                                                                  let CRm :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      8
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let CRn :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      12
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let op1 :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      16
                                                                                                                                                                                                      3)
                                                                                                                                                                                                  let o0 :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      19
                                                                                                                                                                                                      1)
                                                                                                                                                                                                  let L :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      21
                                                                                                                                                                                                      1)
                                                                                                                                                                                                  (decode_msrr_aarch64_instrs_system_register_system_128
                                                                                                                                                                                                    Rt
                                                                                                                                                                                                    op2
                                                                                                                                                                                                    CRm
                                                                                                                                                                                                    CRn
                                                                                                                                                                                                    op1
                                                                                                                                                                                                    o0
                                                                                                                                                                                                    L))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let w__97 ← (( do
                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                           31
                                                                                                                                                                                                           20)) == (0xD53#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        let w__96 ← (( do
                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                          )
                                                                                                                                                                                                          :
                                                                                                                                                                                                          SailM
                                                                                                                                                                                                          Int
                                                                                                                                                                                                          )
                                                                                                                                                                                                        (pure (((w__96 <b 701) : Bool))))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    :
                                                                                                                                                                                                    SailM
                                                                                                                                                                                                    Bool
                                                                                                                                                                                                    )
                                                                                                                                                                                                  if (w__97 : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 701
                                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          0
                                                                                                                                                                                                          5)
                                                                                                                                                                                                      let op2 :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          5
                                                                                                                                                                                                          3)
                                                                                                                                                                                                      let CRm :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          8
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      let CRn :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          12
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      let op1 :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          16
                                                                                                                                                                                                          3)
                                                                                                                                                                                                      let o0 :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          19
                                                                                                                                                                                                          1)
                                                                                                                                                                                                      let L :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          21
                                                                                                                                                                                                          1)
                                                                                                                                                                                                      (decode_mrs_aarch64_instrs_system_register_system
                                                                                                                                                                                                        Rt
                                                                                                                                                                                                        op2
                                                                                                                                                                                                        CRm
                                                                                                                                                                                                        CRn
                                                                                                                                                                                                        op1
                                                                                                                                                                                                        o0
                                                                                                                                                                                                        L))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let w__99 ← (( do
                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               31
                                                                                                                                                                                                               20)) == (0xD51#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__98 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__98 <b 702) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                        )
                                                                                                                                                                                                        :
                                                                                                                                                                                                        SailM
                                                                                                                                                                                                        Bool
                                                                                                                                                                                                        )
                                                                                                                                                                                                      if (w__99 : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 702
                                                                                                                                                                                                          let Rt :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              0
                                                                                                                                                                                                              5)
                                                                                                                                                                                                          let op2 :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              5
                                                                                                                                                                                                              3)
                                                                                                                                                                                                          let CRm :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              8
                                                                                                                                                                                                              4)
                                                                                                                                                                                                          let CRn :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              12
                                                                                                                                                                                                              4)
                                                                                                                                                                                                          let op1 :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              16
                                                                                                                                                                                                              3)
                                                                                                                                                                                                          let o0 :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              19
                                                                                                                                                                                                              1)
                                                                                                                                                                                                          let L :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              21
                                                                                                                                                                                                              1)
                                                                                                                                                                                                          (decode_msr_reg_aarch64_instrs_system_register_system
                                                                                                                                                                                                            Rt
                                                                                                                                                                                                            op2
                                                                                                                                                                                                            CRm
                                                                                                                                                                                                            CRn
                                                                                                                                                                                                            op1
                                                                                                                                                                                                            o0
                                                                                                                                                                                                            L))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let w__101 ← (( do
                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     31
                                                                                                                                                                                                                     19)) == (0b1101010100000#13 : (BitVec 13))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       15
                                                                                                                                                                                                                       12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       4
                                                                                                                                                                                                                       0)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let w__100 ← (( do
                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                  :
                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                (pure (((w__100 <b 703) : Bool))))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                            )
                                                                                                                                                                                                            :
                                                                                                                                                                                                            SailM
                                                                                                                                                                                                            Bool
                                                                                                                                                                                                            )
                                                                                                                                                                                                          if (w__101 : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 703
                                                                                                                                                                                                              let op2 :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  5
                                                                                                                                                                                                                  3)
                                                                                                                                                                                                              let CRm :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  8
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let op1 :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  16
                                                                                                                                                                                                                  3)
                                                                                                                                                                                                              (decode_msr_imm_aarch64_instrs_system_register_cpsr
                                                                                                                                                                                                                op2
                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                op1))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              let w__103 ← (( do
                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         31
                                                                                                                                                                                                                         10)) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           8
                                                                                                                                                                                                                           6)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           4
                                                                                                                                                                                                                           0)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    let w__102 ← (( do
                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                      :
                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                    (pure (((w__102 <b 712) : Bool))))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                )
                                                                                                                                                                                                                :
                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                )
                                                                                                                                                                                                              if (w__103 : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 712
                                                                                                                                                                                                                  let op2 :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      5
                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                  let CRm :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      8
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  (decode_pacia_aarch64_instrs_integer_pac_pacia_hint
                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                    CRm))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  let w__105 ← (( do
                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                             31
                                                                                                                                                                                                                             10)) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               8
                                                                                                                                                                                                                               6)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               4
                                                                                                                                                                                                                               0)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        let w__104 ← (( do
                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                          :
                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                        (pure (((w__104 <b 714) : Bool))))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                    :
                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                  if (w__105 : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 714
                                                                                                                                                                                                                      let op2 :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          5
                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                      let CRm :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          8
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      (decode_pacib_aarch64_instrs_integer_pac_pacib_hint
                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                        CRm))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      let w__107 ← (( do
                                                                                                                                                                                                                        if (((__opcode == 0b11010101000000110011000011111111#32) : Bool) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            let w__106 ← (( do
                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                              :
                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                            (pure (((w__106 <b 768) : Bool))))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                        :
                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                      if (w__107 : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 768
                                                                                                                                                                                                                          let opc :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              5
                                                                                                                                                                                                                              2)
                                                                                                                                                                                                                          let CRm :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              8
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                       10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     11)])) != 0#1)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (decode_sb_aarch64_instrs_system_barriers_sb
                                                                                                                                                                                                                                opc
                                                                                                                                                                                                                                CRm)))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          let w__109 ← (( do
                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     31
                                                                                                                                                                                                                                     21)) == (0b11010100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     4
                                                                                                                                                                                                                                     0)) == (0b00011#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let w__108 ← (( do
                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                (pure (((w__108 <b 846) : Bool))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                            :
                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                          if (w__109 : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 846
                                                                                                                                                                                                                              let imm16 :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  5
                                                                                                                                                                                                                                  16)
                                                                                                                                                                                                                              (decode_smc_aarch64_instrs_system_exceptions_runtime_smc
                                                                                                                                                                                                                                imm16))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              let w__111 ← (( do
                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                         21)) == (0b11010100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         4
                                                                                                                                                                                                                                         0)) == (0b00001#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    let w__110 ← (( do
                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                    (pure (((w__110 <b 999) : Bool))))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                              if (w__111 : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 999
                                                                                                                                                                                                                                  let imm16 :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                      16)
                                                                                                                                                                                                                                  (decode_svc_aarch64_instrs_system_exceptions_runtime_svc
                                                                                                                                                                                                                                    imm16))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  let w__113 ← (( do
                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                           31
                                                                                                                                                                                                                                           19)) == (0b1101010100001#13 : (BitVec 13))) : Bool) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        let w__112 ← (( do
                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                        (pure (((w__112 <b 1004) : Bool))))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                  if (w__113 : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 1004
                                                                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                      let op2 :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                      let CRm :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          8
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let CRn :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let op1 :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                      let L :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          21
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      (decode_sys_aarch64_instrs_system_sysops
                                                                                                                                                                                                                                        Rt
                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                        L))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      let w__115 ← (( do
                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                               31
                                                                                                                                                                                                                                               19)) == (0b1101010100101#13 : (BitVec 13))) : Bool) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            let w__114 ← (( do
                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                            (pure (((w__114 <b 1005) : Bool))))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                      if (w__115 : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 1005
                                                                                                                                                                                                                                          let Rt :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                          let op2 :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              5
                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                          let CRm :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              8
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let CRn :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let op1 :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                          let L :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              21
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          (decode_sysl_aarch64_instrs_system_sysops
                                                                                                                                                                                                                                            Rt
                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                            L))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          let w__117 ← (( do
                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                   31
                                                                                                                                                                                                                                                   19)) == (0b1101010101001#13 : (BitVec 13))) : Bool) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                let w__116 ← (( do
                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                (pure (((w__116 <b 1006) : Bool))))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                          if (w__117 : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 1006
                                                                                                                                                                                                                                              let Rt :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                              let op2 :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  5
                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                              let CRm :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  8
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let CRn :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let op1 :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                              let L :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  21
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              (decode_sysp_aarch64_instrs_system_sysops_128
                                                                                                                                                                                                                                                Rt
                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                L))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              let w__119 ← (( do
                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       30
                                                                                                                                                                                                                                                       24)) == (0b0110111#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    let w__118 ← (( do
                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                    (pure (((w__118 <b 1009) : Bool))))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                              if (w__119 : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 1009
                                                                                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                      5)
                                                                                                                                                                                                                                                  let imm14 :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                                      14)
                                                                                                                                                                                                                                                  let b40 :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      19
                                                                                                                                                                                                                                                      5)
                                                                                                                                                                                                                                                  let op :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      24
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  let b5 :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  (decode_tbnz_aarch64_instrs_branch_conditional_test
                                                                                                                                                                                                                                                    Rt
                                                                                                                                                                                                                                                    imm14
                                                                                                                                                                                                                                                    b40
                                                                                                                                                                                                                                                    op
                                                                                                                                                                                                                                                    b5))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  let w__121 ← (( do
                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           30
                                                                                                                                                                                                                                                           24)) == (0b0110110#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        let w__120 ← (( do
                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                        (pure (((w__120 <b 1010) : Bool))))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                  if (w__121 : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 1010
                                                                                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                      let imm14 :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                                          14)
                                                                                                                                                                                                                                                      let b40 :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          19
                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                      let op :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          24
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      let b5 :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          31
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      (decode_tbz_aarch64_instrs_branch_conditional_test
                                                                                                                                                                                                                                                        Rt
                                                                                                                                                                                                                                                        imm14
                                                                                                                                                                                                                                                        b40
                                                                                                                                                                                                                                                        op
                                                                                                                                                                                                                                                        b5))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      let w__123 ← (( do
                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 31
                                                                                                                                                                                                                                                                 21)) == (0b11010100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 4
                                                                                                                                                                                                                                                                 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            let w__122 ← (( do
                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                            (pure (((w__122 <b 1011) : Bool))))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                      if (w__123 : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 1011
                                                                                                                                                                                                                                                          let imm16 :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              5
                                                                                                                                                                                                                                                              16)
                                                                                                                                                                                                                                                          (decode_tcancel_aarch64_instrs_system_tme_tcancel
                                                                                                                                                                                                                                                            imm16))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          let w__125 ← (( do
                                                                                                                                                                                                                                                            if (((__opcode == 0b11010101000000110011000001111111#32) : Bool) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                let w__124 ← (( do
                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                (pure (((w__124 <b 1012) : Bool))))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                          if (w__125 : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 1012
                                                                                                                                                                                                                                                              (decode_tcommit_aarch64_instrs_system_tme_tcommit
                                                                                                                                                                                                                                                                ()))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              let w__127 ← (( do
                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       31
                                                                                                                                                                                                                                                                       5)) == (0b110101010010001100110000011#27 : (BitVec 27))) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    let w__126 ← (( do
                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                    (pure (((w__126 <b 1015) : Bool))))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                              if (w__127 : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 1015
                                                                                                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                      5)
                                                                                                                                                                                                                                                                  (decode_tstart_aarch64_instrs_system_tme_tstart
                                                                                                                                                                                                                                                                    Rt))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  let w__129 ← (( do
                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           31
                                                                                                                                                                                                                                                                           5)) == (0b110101010010001100110001011#27 : (BitVec 27))) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let w__128 ← (( do
                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                        (pure (((w__128 <b 1016) : Bool))))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                  if (w__129 : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 1016
                                                                                                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                                      (decode_ttest_aarch64_instrs_system_tme_ttest
                                                                                                                                                                                                                                                                        Rt))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      let w__131 ← (( do
                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                               31
                                                                                                                                                                                                                                                                               5)) == (0b110101010000001100010000000#27 : (BitVec 27))) : Bool) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            let w__130 ← (( do
                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                            (pure (((w__130 <b 1028) : Bool))))
                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                      if (w__131 : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 1028
                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                                                          (decode_wfet_aarch64_instrs_system_sysinstwithreg_wfet
                                                                                                                                                                                                                                                                            Rd))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          let w__133 ← (( do
                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                   31
                                                                                                                                                                                                                                                                                   5)) == (0b110101010000001100010000001#27 : (BitVec 27))) : Bool) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                let w__132 ← (( do
                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                (pure (((w__132 <b 1029) : Bool))))
                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                          if (w__133 : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 1029
                                                                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                                                              (decode_wfit_aarch64_instrs_system_sysinstwithreg_wfit
                                                                                                                                                                                                                                                                                Rd))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              let w__135 ← (( do
                                                                                                                                                                                                                                                                                if (((__opcode == 0b11010101000000000100000000111111#32) : Bool) : Bool)
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                    let w__134 ← (( do
                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                    (pure (((w__134 <b 1030) : Bool))))
                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                              if (w__135 : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 1030
                                                                                                                                                                                                                                                                                  let CRm :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      8
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             11)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (decode_xaflag_aarch64_instrs_integer_flags_xaflag
                                                                                                                                                                                                                                                                                        CRm)))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  let w__137 ← (( do
                                                                                                                                                                                                                                                                                    if (((__opcode == 0b11010101000000110010000011111111#32) : Bool) : Bool)
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                        let w__136 ← (( do
                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                        (pure (((w__136 <b 1033) : Bool))))
                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                  if (w__137 : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 1033
                                                                                                                                                                                                                                                                                      (decode_xpac_aarch64_instrs_integer_pac_strip_hint
                                                                                                                                                                                                                                                                                        ()))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    sailThrow ((Error_Undefined
                                                                                                                                                                                                                                                                                      ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
