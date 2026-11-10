import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0146
import ArmFull.Fn.M0581
import ArmFull.Fn.M0842
import ArmFull.Fn.M1008
import ArmFull.Fn.M1049
import ArmFull.Fn.M1050
import ArmFull.Fn.M1051
import ArmFull.Fn.M1059
import ArmFull.Fn.M1060
import ArmFull.Fn.M1073
import ArmFull.Fn.M1089
import ArmFull.Fn.M1090
import ArmFull.Fn.M1091
import ArmFull.Fn.M1092
import ArmFull.Fn.M1093
import ArmFull.Fn.M1094
import ArmFull.Fn.M1095
import ArmFull.Fn.M1143
import ArmFull.Fn.M1144
import ArmFull.Fn.M1145
import ArmFull.Fn.M1146
import ArmFull.Fn.M1147
import ArmFull.Fn.M1148
import ArmFull.Fn.M1182
import ArmFull.Fn.M1283
import ArmFull.Fn.M1287
import ArmFull.Fn.M1288
import ArmFull.Fn.M1290
import ArmFull.Fn.M1467
import ArmFull.Fn.M1468

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

def decode_mrrs_aarch64_instrs_system_register_system_128 (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveSysReg128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat (BitVec.addInt Rt 1))
  let sys_op0 : Int := (2 +i (BitVec.toNat o0))
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system_128 read (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) (Sail.Int.toNatChecked (sys_op0))
    (Sail.Int.toNatChecked (sys_op1)) (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)))


def decode_msrr_aarch64_instrs_system_register_system_128 (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveSysReg128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat (BitVec.addInt Rt 1))
  let sys_op0 : Int := (2 +i (BitVec.toNat o0))
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system_128 read (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) (Sail.Int.toNatChecked (sys_op0))
    (Sail.Int.toNatChecked (sys_op1)) (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)))


/-- Type quantifiers: k_has_result : Bool, sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 :
  Nat, sys_op2 : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  sys_op0 = 1 ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_sysops (has_result : Bool) (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) : SailM Unit := do
  if (has_result : Bool)
  then
    (do
      (AArch64_SysInstrWithResult sys_op0 sys_op1 sys_crn sys_crm sys_op2 t))
  else
    (do
      (AArch64_SysInstr sys_op0 sys_op1 sys_crn sys_crm sys_op2 t))


/-- Type quantifiers: pc : Int -/
def __DecodeA32_SysASIMDFP (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                 __opcode 15 8)) == (0x5E#8 : (BitVec 8)))))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__0 <b 2912) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg SEE 2912
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let imm8 := (BitVec.slice __opcode 0 8)
      (decode_aarch32_instrs_LDC_i_A1enc_A_txt cond P U W Rn imm8))
  else
    (do
      let w__5 ← (( do
        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 22 22)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                   __opcode 20 8)) == (0b1111101011110#13 : (BitVec 13))))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__3 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__3 <b 2914) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          writeReg SEE 2914
          let cond := (BitVec.slice __opcode 28 4)
          let P := (BitVec.slice __opcode 24 1)
          let U := (BitVec.slice __opcode 23 1)
          let W := (BitVec.slice __opcode 21 1)
          let imm8 := (BitVec.slice __opcode 0 8)
          (decode_aarch32_instrs_LDC_l_A1enc_A_txt cond P U W imm8))
      else
        (do
          let w__8 ← (( do
            if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 20 20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 11 9)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 3001) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              writeReg SEE 3001
              let cond := (BitVec.slice __opcode 28 4)
              let opc1 := (BitVec.slice __opcode 21 3)
              let CRn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let coproc := (BitVec.slice __opcode 8 1)
              let opc2 := (BitVec.slice __opcode 5 3)
              let CRm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_MCR_A1enc_A_txt cond opc1 CRn Rt coproc opc2 CRm))
          else
            (do
              let w__11 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0xC4#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 11 9)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__9 <b 3003) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  writeReg SEE 3003
                  let cond := (BitVec.slice __opcode 28 4)
                  let Rt2 := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let coproc := (BitVec.slice __opcode 8 1)
                  let opc1 := (BitVec.slice __opcode 4 4)
                  let CRm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_MCRR_A1enc_A_txt cond Rt2 Rt coproc opc1 CRm))
              else
                (do
                  let w__14 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 20 20)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 11 9)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__12 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__12 <b 3023) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      writeReg SEE 3023
                      let cond := (BitVec.slice __opcode 28 4)
                      let opc1 := (BitVec.slice __opcode 21 3)
                      let CRn := (BitVec.slice __opcode 16 4)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let coproc := (BitVec.slice __opcode 8 1)
                      let opc2 := (BitVec.slice __opcode 5 3)
                      let CRm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_MRC_A1enc_A_txt cond opc1 CRn Rt coproc opc2 CRm))
                  else
                    (do
                      let w__17 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27
                                 20)) == (0xC5#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 11 9)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__15 <b 3025) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          writeReg SEE 3025
                          let cond := (BitVec.slice __opcode 28 4)
                          let Rt2 := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let coproc := (BitVec.slice __opcode 8 1)
                          let opc1 := (BitVec.slice __opcode 4 4)
                          let CRm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_MRRC_A1enc_A_txt cond Rt2 Rt coproc opc1 CRm))
                      else
                        (do
                          let w__20 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     27 25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 15 8)) == (0x5E#8 : (BitVec 8)))))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__18 <b 3184) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__20 : Bool)
                          then
                            (do
                              writeReg SEE 3184
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let imm8 := (BitVec.slice __opcode 0 8)
                              (decode_aarch32_instrs_STC_A1enc_A_txt cond P U W Rn imm8))
                          else
                            (do
                              let w__23 ← (( do
                                if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 27 24)) == (0xF#4 : (BitVec 4))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__21 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__21 <b 3251) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__23 : Bool)
                              then
                                (do
                                  writeReg SEE 3251
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let imm24 := (BitVec.slice __opcode 0 24)
                                  (decode_aarch32_instrs_SVC_A1enc_A_txt cond imm24))
                              else
                                (do
                                  let w__26 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                             __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 21 16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 7 6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__24 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__24 <b 3361) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__26 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3361
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let size := (BitVec.slice __opcode 8 2)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VABS_A2enc_A_txt cond D Vd size M Vm))
                                  else
                                    (do
                                      let w__29 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                 __opcode 27 23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__27 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__27 <b 3367) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__29 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3367
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Vn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let size := (BitVec.slice __opcode 8 2)
                                          let N := (BitVec.slice __opcode 7 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VADD_f_A2enc_A_txt cond D Vn Vd
                                            size N M Vm))
                                      else
                                        (do
                                          let w__32 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                     __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 21 16)) == (0b110100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__30 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__30 <b 3412) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__32 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3412
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let size := (BitVec.slice __opcode 8 2)
                                              let E := (BitVec.slice __opcode 7 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VCMP_A1enc_A_txt cond D Vd size
                                                E M Vm))
                                          else
                                            (do
                                              let w__35 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                         __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 21 16)) == (0b110101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 11 10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                             __opcode 6 0)) == (0b1000000#7 : (BitVec 7)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__33 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__33 <b 3413) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__35 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3413
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let size := (BitVec.slice __opcode 8 2)
                                                  let E := (BitVec.slice __opcode 7 1)
                                                  if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 3)])) != 0#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_VCMP_A2enc_A_txt cond D
                                                        Vd size E)))
                                              else
                                                (do
                                                  let w__38 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                             __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                               __opcode 21 17)) == (0b11001#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 11 9)) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__36 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__36 <b 3418) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__38 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3418
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let op := (BitVec.slice __opcode 16 1)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let sz := (BitVec.slice __opcode 8 1)
                                                      let T := (BitVec.slice __opcode 7 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VCVTB_A1enc_A_txt cond
                                                        D op Vd sz T M Vm))
                                                  else
                                                    (do
                                                      let w__41 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                 __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 21 16)) == (0b110111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 11 9)) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 7 6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__39 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__39 <b 3420) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__41 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3420
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let size := (BitVec.slice __opcode 8 2)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VCVT_ds_A1enc_A_txt
                                                            cond D Vd size M Vm))
                                                      else
                                                        (do
                                                          let w__44 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                     __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 21 19)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__42 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__42 <b 3426) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__44 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3426
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let opc2 :=
                                                                (BitVec.slice __opcode 16 3)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let size :=
                                                                (BitVec.slice __opcode 8 2)
                                                              let op := (BitVec.slice __opcode 7 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VCVT_iv_A1enc_A_txt
                                                                cond D opc2 Vd size op M Vm))
                                                          else
                                                            (do
                                                              let w__47 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                         __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 21 19)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 17 17)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__45 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__45 <b 3430) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__47 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3430
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let op :=
                                                                    (BitVec.slice __opcode 18 1)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 16 1)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let sf :=
                                                                    (BitVec.slice __opcode 8 2)
                                                                  let sx :=
                                                                    (BitVec.slice __opcode 7 1)
                                                                  let i :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let imm4 :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VCVT_xv_A1enc_A_txt
                                                                    cond D op U Vd sf sx i imm4))
                                                              else
                                                                (do
                                                                  let w__50 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                             __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__48 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__48 <b 3432) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__50 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3432
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Vn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 8 2)
                                                                      let N :=
                                                                        (BitVec.slice __opcode 7 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VDIV_A1enc_A_txt
                                                                        cond D Vn Vd size N M Vm))
                                                                  else
                                                                    (do
                                                                      let w__53 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                 __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 20 20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0xB#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 0)) == (0b10000#5 : (BitVec 5))))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__51 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__51 <b 3434) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__53 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3434
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let B :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let D :=
                                                                            (BitVec.slice __opcode 7
                                                                              1)
                                                                          let E :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 3)])) != 0#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_VDUP_r_A1enc_A_txt
                                                                                cond B Q Vd Rt D E)))
                                                                      else
                                                                        (do
                                                                          let w__56 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                     __opcode 27 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__54 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__54 <b 3443) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__56 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3443
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Vn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 2)
                                                                              let N :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 1)
                                                                              let op :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VFMA_A2enc_A_txt
                                                                                cond D Vn Vd size N
                                                                                op M Vm))
                                                                          else
                                                                            (do
                                                                              let w__59 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                         __opcode 27
                                                                                         23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__57 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__57 <b 3446) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__59 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3446
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 2)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VFNMA_A1enc_A_txt
                                                                                    cond D Vn Vd
                                                                                    size N op M Vm))
                                                                              else
                                                                                (do
                                                                                  let w__62 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__60 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__60 <b 3498) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__62 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3498
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let P :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          24 1)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let W :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let imm8 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          8)
                                                                                      (decode_aarch32_instrs_VLDM_A1enc_A_txt
                                                                                        cond P U D W
                                                                                        Rn Vd imm8))
                                                                                  else
                                                                                    (do
                                                                                      let w__65 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   20
                                                                                                   20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                   __opcode
                                                                                                   28
                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__63 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__63 <b 3499) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__65 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3499
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let P :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              24 1)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 1)
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let W :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              21 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let imm8 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 8)
                                                                                          (decode_aarch32_instrs_VLDM_A2enc_A_txt
                                                                                            cond P U
                                                                                            D W Rn
                                                                                            Vd imm8))
                                                                                      else
                                                                                        (do
                                                                                          let w__68 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     27
                                                                                                     24)) == (0xD#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                       __opcode
                                                                                                       28
                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__66 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__66 <b 3502) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__68 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3502
                                                                                              let cond :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  28
                                                                                                  4)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  23
                                                                                                  1)
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  2)
                                                                                              let imm8 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  8)
                                                                                              (decode_aarch32_instrs_VLDR_A1enc_A_txt
                                                                                                cond
                                                                                                U D
                                                                                                Rn
                                                                                                Vd
                                                                                                size
                                                                                                imm8))
                                                                                          else
                                                                                            (do
                                                                                              let w__71 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         27
                                                                                                         23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__69 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__69 <b 3509) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__71 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3509
                                                                                                  let cond :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      4)
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Vn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      2)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      1)
                                                                                                  let op :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      1)
                                                                                                  let M :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      1)
                                                                                                  let Vm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VMLA_f_A2enc_A_txt
                                                                                                    cond
                                                                                                    D
                                                                                                    Vn
                                                                                                    Vd
                                                                                                    size
                                                                                                    N
                                                                                                    op
                                                                                                    M
                                                                                                    Vm))
                                                                                              else
                                                                                                (do
                                                                                                  let w__73 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 11
                                                                                                                 6)) == (0b101001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__72 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__72 <b 3520) : Bool))))
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
                                                                                                      writeReg SEE 3520
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let M :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          1)
                                                                                                      let Vm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VMOVX_A1enc_A_txt
                                                                                                        D
                                                                                                        Vd
                                                                                                        M
                                                                                                        Vm))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__75 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     6)) == (0b101011#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__74 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__74 <b 3522) : Bool))))
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
                                                                                                          writeReg SEE 3522
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let Vm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VINS_A1enc_A_txt
                                                                                                            D
                                                                                                            Vd
                                                                                                            M
                                                                                                            Vm))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__78 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     27
                                                                                                                     21)) == (0b1100010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       6)) == (0b101100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                       __opcode
                                                                                                                       28
                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__76 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__76 <b 3524) : Bool))))
                                                                                                                else
                                                                                                                  (pure false))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__78 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3524
                                                                                                              let cond :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  28
                                                                                                                  4)
                                                                                                              let op :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  20
                                                                                                                  1)
                                                                                                              let Rt2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let M :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  1)
                                                                                                              let Vm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_VMOV_d_A1enc_A_txt
                                                                                                                cond
                                                                                                                op
                                                                                                                Rt2
                                                                                                                Rt
                                                                                                                M
                                                                                                                Vm))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__81 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         27
                                                                                                                         23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             7
                                                                                                                             4)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                           __opcode
                                                                                                                           28
                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__79 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__79 <b 3527) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false))
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
                                                                                                                  writeReg SEE 3527
                                                                                                                  let cond :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      28
                                                                                                                      4)
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let imm4H :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      2)
                                                                                                                  let imm4L :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             7)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             5)])) != 0#1)) : Bool)
                                                                                                                  then
                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                      ()))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      (decode_aarch32_instrs_VMOV_i_A2enc_A_txt
                                                                                                                        cond
                                                                                                                        D
                                                                                                                        imm4H
                                                                                                                        Vd
                                                                                                                        size
                                                                                                                        imm4L)))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__84 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             27
                                                                                                                             21)) == (0b1110000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               8)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               6
                                                                                                                               0)) == (0b0010000#7 : (BitVec 7))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                               __opcode
                                                                                                                               28
                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__82 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__82 <b 3540) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__84 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3540
                                                                                                                      let cond :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          28
                                                                                                                          4)
                                                                                                                      let op :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          20
                                                                                                                          1)
                                                                                                                      let Vn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Rt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let N :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          7
                                                                                                                          1)
                                                                                                                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 3)])) != 0#1)) : Bool)
                                                                                                                      then
                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                          ()))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          (decode_aarch32_instrs_VMOV_h_A1enc_A_txt
                                                                                                                            cond
                                                                                                                            op
                                                                                                                            Vn
                                                                                                                            Rt
                                                                                                                            N)))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__87 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 27
                                                                                                                                 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       7
                                                                                                                                       6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                   __opcode
                                                                                                                                   28
                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__85 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__85 <b 3542) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false))
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
                                                                                                                          writeReg SEE 3542
                                                                                                                          let cond :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              28
                                                                                                                              4)
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Vd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              2)
                                                                                                                          let M :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              1)
                                                                                                                          let Vm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_VMOV_r_A2enc_A_txt
                                                                                                                            cond
                                                                                                                            D
                                                                                                                            Vd
                                                                                                                            size
                                                                                                                            M
                                                                                                                            Vm))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__90 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     27
                                                                                                                                     23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       20
                                                                                                                                       20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         11
                                                                                                                                         8)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         4
                                                                                                                                         0)) == (0b10000#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                       __opcode
                                                                                                                                       28
                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__88 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__88 <b 3544) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__90 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3544
                                                                                                                              let cond :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  28
                                                                                                                                  4)
                                                                                                                              let opc1 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  21
                                                                                                                                  2)
                                                                                                                              let Vd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Rt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let D :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  7
                                                                                                                                  1)
                                                                                                                              let opc2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  2)
                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         3)])) != 0#1)) : Bool)
                                                                                                                              then
                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                  ()))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  (decode_aarch32_instrs_VMOV_rs_A1enc_A_txt
                                                                                                                                    cond
                                                                                                                                    opc1
                                                                                                                                    Vd
                                                                                                                                    Rt
                                                                                                                                    D
                                                                                                                                    opc2)))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__93 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         27
                                                                                                                                         21)) == (0b1110000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           11
                                                                                                                                           8)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           6
                                                                                                                                           0)) == (0b0010000#7 : (BitVec 7))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                           __opcode
                                                                                                                                           28
                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__91 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__91 <b 3546) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false))
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
                                                                                                                                  writeReg SEE 3546
                                                                                                                                  let cond :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      28
                                                                                                                                      4)
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      20
                                                                                                                                      1)
                                                                                                                                  let Vn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let N :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      7
                                                                                                                                      1)
                                                                                                                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             3)])) != 0#1)) : Bool)
                                                                                                                                  then
                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                      ()))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      (decode_aarch32_instrs_VMOV_s_A1enc_A_txt
                                                                                                                                        cond
                                                                                                                                        op
                                                                                                                                        Vn
                                                                                                                                        Rt
                                                                                                                                        N)))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__96 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             27
                                                                                                                                             24)) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               20
                                                                                                                                               20)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 11
                                                                                                                                                 8)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 0)) == (0b10000#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                               __opcode
                                                                                                                                               28
                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__94 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__94 <b 3548) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__96 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3548
                                                                                                                                      let cond :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          28
                                                                                                                                          4)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          23
                                                                                                                                          1)
                                                                                                                                      let opc1 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          21
                                                                                                                                          2)
                                                                                                                                      let Vn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Rt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          4)
                                                                                                                                      let N :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          7
                                                                                                                                          1)
                                                                                                                                      let opc2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          2)
                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 3)])) != 0#1)) : Bool)
                                                                                                                                      then
                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                          ()))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          (decode_aarch32_instrs_VMOV_sr_A1enc_A_txt
                                                                                                                                            cond
                                                                                                                                            U
                                                                                                                                            opc1
                                                                                                                                            Vn
                                                                                                                                            Rt
                                                                                                                                            N
                                                                                                                                            opc2)))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__99 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 27
                                                                                                                                                 21)) == (0b1100010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   11
                                                                                                                                                   6)) == (0b101000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                   __opcode
                                                                                                                                                   28
                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__97 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__97 <b 3550) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false))
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
                                                                                                                                          writeReg SEE 3550
                                                                                                                                          let cond :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              28
                                                                                                                                              4)
                                                                                                                                          let op :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              20
                                                                                                                                              1)
                                                                                                                                          let Rt2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Rt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              4)
                                                                                                                                          let M :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              1)
                                                                                                                                          let Vm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              4)
                                                                                                                                          (decode_aarch32_instrs_VMOV_ss_A1enc_A_txt
                                                                                                                                            cond
                                                                                                                                            op
                                                                                                                                            Rt2
                                                                                                                                            Rt
                                                                                                                                            M
                                                                                                                                            Vm))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__102 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     27
                                                                                                                                                     23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         11
                                                                                                                                                         10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           6
                                                                                                                                                           6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           4
                                                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                       __opcode
                                                                                                                                                       28
                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__100 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__100 <b 3553) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__102 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3553
                                                                                                                                              let cond :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  28
                                                                                                                                                  4)
                                                                                                                                              let D :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  1)
                                                                                                                                              let Vn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Vd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  4)
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  8
                                                                                                                                                  2)
                                                                                                                                              let N :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  7
                                                                                                                                                  1)
                                                                                                                                              let M :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  1)
                                                                                                                                              let Vm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  4)
                                                                                                                                              (decode_aarch32_instrs_VMUL_f_A2enc_A_txt
                                                                                                                                                cond
                                                                                                                                                D
                                                                                                                                                Vn
                                                                                                                                                Vd
                                                                                                                                                size
                                                                                                                                                N
                                                                                                                                                M
                                                                                                                                                Vm))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__105 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         27
                                                                                                                                                         23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           16)) == (0b110001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             11
                                                                                                                                                             10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               7
                                                                                                                                                               6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               4
                                                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                           __opcode
                                                                                                                                                           28
                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__103 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__103 <b 3573) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false))
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
                                                                                                                                                  writeReg SEE 3573
                                                                                                                                                  let cond :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      28
                                                                                                                                                      4)
                                                                                                                                                  let D :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      1)
                                                                                                                                                  let Vd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      4)
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      8
                                                                                                                                                      2)
                                                                                                                                                  let M :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      1)
                                                                                                                                                  let Vm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_aarch32_instrs_VNEG_A2enc_A_txt
                                                                                                                                                    cond
                                                                                                                                                    D
                                                                                                                                                    Vd
                                                                                                                                                    size
                                                                                                                                                    M
                                                                                                                                                    Vm))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__108 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             27
                                                                                                                                                             23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 11
                                                                                                                                                                 10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 4
                                                                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                               __opcode
                                                                                                                                                               28
                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__106 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__106 <b 3576) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__108 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3576
                                                                                                                                                      let cond :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          28
                                                                                                                                                          4)
                                                                                                                                                      let D :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          1)
                                                                                                                                                      let Vn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          4)
                                                                                                                                                      let Vd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          4)
                                                                                                                                                      let size :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          8
                                                                                                                                                          2)
                                                                                                                                                      let N :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          7
                                                                                                                                                          1)
                                                                                                                                                      let op :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          6
                                                                                                                                                          1)
                                                                                                                                                      let M :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          1)
                                                                                                                                                      let Vm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          4)
                                                                                                                                                      (decode_aarch32_instrs_VNMLA_A1enc_A_txt
                                                                                                                                                        cond
                                                                                                                                                        D
                                                                                                                                                        Vn
                                                                                                                                                        Vd
                                                                                                                                                        size
                                                                                                                                                        N
                                                                                                                                                        op
                                                                                                                                                        M
                                                                                                                                                        Vm))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__111 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 27
                                                                                                                                                                 23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     11
                                                                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       6
                                                                                                                                                                       6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       4
                                                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                   __opcode
                                                                                                                                                                   28
                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__109 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__109 <b 3577) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false))
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
                                                                                                                                                          writeReg SEE 3577
                                                                                                                                                          let cond :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              28
                                                                                                                                                              4)
                                                                                                                                                          let D :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              1)
                                                                                                                                                          let Vn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let Vd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              4)
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              8
                                                                                                                                                              2)
                                                                                                                                                          let N :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              7
                                                                                                                                                              1)
                                                                                                                                                          let M :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              1)
                                                                                                                                                          let Vm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              4)
                                                                                                                                                          (decode_aarch32_instrs_VNMLA_A2enc_A_txt
                                                                                                                                                            cond
                                                                                                                                                            D
                                                                                                                                                            Vn
                                                                                                                                                            Vd
                                                                                                                                                            size
                                                                                                                                                            N
                                                                                                                                                            M
                                                                                                                                                            Vm))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__114 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     27
                                                                                                                                                                     23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       16)) == (0b110001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         11
                                                                                                                                                                         10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           7
                                                                                                                                                                           6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           4
                                                                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                       __opcode
                                                                                                                                                                       28
                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__112 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__112 <b 3686) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__114 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3686
                                                                                                                                                              let cond :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  28
                                                                                                                                                                  4)
                                                                                                                                                              let D :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  1)
                                                                                                                                                              let Vd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  4)
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  8
                                                                                                                                                                  2)
                                                                                                                                                              let M :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  1)
                                                                                                                                                              let Vm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  4)
                                                                                                                                                              (decode_aarch32_instrs_VSQRT_A1enc_A_txt
                                                                                                                                                                cond
                                                                                                                                                                D
                                                                                                                                                                Vd
                                                                                                                                                                size
                                                                                                                                                                M
                                                                                                                                                                Vm))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__117 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         27
                                                                                                                                                                         25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           20
                                                                                                                                                                           20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           11
                                                                                                                                                                           8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                           __opcode
                                                                                                                                                                           28
                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__115 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__115 <b 3732) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false))
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
                                                                                                                                                                  writeReg SEE 3732
                                                                                                                                                                  let cond :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      28
                                                                                                                                                                      4)
                                                                                                                                                                  let P :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      24
                                                                                                                                                                      1)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      23
                                                                                                                                                                      1)
                                                                                                                                                                  let D :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      1)
                                                                                                                                                                  let W :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      21
                                                                                                                                                                      1)
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      4)
                                                                                                                                                                  let Vd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      4)
                                                                                                                                                                  let imm8 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      8)
                                                                                                                                                                  (decode_aarch32_instrs_VSTM_A1enc_A_txt
                                                                                                                                                                    cond
                                                                                                                                                                    P
                                                                                                                                                                    U
                                                                                                                                                                    D
                                                                                                                                                                    W
                                                                                                                                                                    Rn
                                                                                                                                                                    Vd
                                                                                                                                                                    imm8))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__120 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             27
                                                                                                                                                                             25)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               20
                                                                                                                                                                               20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               11
                                                                                                                                                                               8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                               __opcode
                                                                                                                                                                               28
                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__118 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__118 <b 3733) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__120 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3733
                                                                                                                                                                      let cond :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          28
                                                                                                                                                                          4)
                                                                                                                                                                      let P :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          24
                                                                                                                                                                          1)
                                                                                                                                                                      let U :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          23
                                                                                                                                                                          1)
                                                                                                                                                                      let D :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          1)
                                                                                                                                                                      let W :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          21
                                                                                                                                                                          1)
                                                                                                                                                                      let Rn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          4)
                                                                                                                                                                      let Vd :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          4)
                                                                                                                                                                      let imm8 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          8)
                                                                                                                                                                      (decode_aarch32_instrs_VSTM_A2enc_A_txt
                                                                                                                                                                        cond
                                                                                                                                                                        P
                                                                                                                                                                        U
                                                                                                                                                                        D
                                                                                                                                                                        W
                                                                                                                                                                        Rn
                                                                                                                                                                        Vd
                                                                                                                                                                        imm8))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__123 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 27
                                                                                                                                                                                 24)) == (0xD#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   21
                                                                                                                                                                                   20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   11
                                                                                                                                                                                   10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   28
                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__121 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__121 <b 3736) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false))
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
                                                                                                                                                                          writeReg SEE 3736
                                                                                                                                                                          let cond :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              28
                                                                                                                                                                              4)
                                                                                                                                                                          let U :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              23
                                                                                                                                                                              1)
                                                                                                                                                                          let D :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              22
                                                                                                                                                                              1)
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              4)
                                                                                                                                                                          let Vd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
                                                                                                                                                                              4)
                                                                                                                                                                          let size :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              8
                                                                                                                                                                              2)
                                                                                                                                                                          let imm8 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              8)
                                                                                                                                                                          (decode_aarch32_instrs_VSTR_A1enc_A_txt
                                                                                                                                                                            cond
                                                                                                                                                                            U
                                                                                                                                                                            D
                                                                                                                                                                            Rn
                                                                                                                                                                            Vd
                                                                                                                                                                            size
                                                                                                                                                                            imm8))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__126 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     27
                                                                                                                                                                                     23)) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       21
                                                                                                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         11
                                                                                                                                                                                         10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           6
                                                                                                                                                                                           6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           4
                                                                                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       28
                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__124 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__124 <b 3739) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__126 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3739
                                                                                                                                                                              let cond :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  28
                                                                                                                                                                                  4)
                                                                                                                                                                              let D :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  22
                                                                                                                                                                                  1)
                                                                                                                                                                              let Vn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  16
                                                                                                                                                                                  4)
                                                                                                                                                                              let Vd :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  12
                                                                                                                                                                                  4)
                                                                                                                                                                              let size :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  8
                                                                                                                                                                                  2)
                                                                                                                                                                              let N :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  7
                                                                                                                                                                                  1)
                                                                                                                                                                              let M :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  5
                                                                                                                                                                                  1)
                                                                                                                                                                              let Vm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  4)
                                                                                                                                                                              (decode_aarch32_instrs_VSUB_f_A2enc_A_txt
                                                                                                                                                                                cond
                                                                                                                                                                                D
                                                                                                                                                                                Vn
                                                                                                                                                                                Vd
                                                                                                                                                                                size
                                                                                                                                                                                N
                                                                                                                                                                                M
                                                                                                                                                                                Vm))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__129 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         27
                                                                                                                                                                                         20)) == (0xEF#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         11
                                                                                                                                                                                         0)) == (0xA10#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           28
                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__127 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__127 <b 3796) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false))
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
                                                                                                                                                                                  writeReg SEE 3796
                                                                                                                                                                                  let cond :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      28
                                                                                                                                                                                      4)
                                                                                                                                                                                  let reg :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      12
                                                                                                                                                                                      4)
                                                                                                                                                                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             3)])) != 0#1)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                      ()))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      (decode_aarch32_instrs_VMRS_A1enc_AS_txt
                                                                                                                                                                                        cond
                                                                                                                                                                                        reg
                                                                                                                                                                                        Rt)))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__132 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             27
                                                                                                                                                                                             20)) == (0xEE#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             11
                                                                                                                                                                                             0)) == (0xA10#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               28
                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__130 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__130 <b 3798) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__132 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 3798
                                                                                                                                                                                      let cond :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          28
                                                                                                                                                                                          4)
                                                                                                                                                                                      let reg :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          16
                                                                                                                                                                                          4)
                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          12
                                                                                                                                                                                          4)
                                                                                                                                                                                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 3)])) != 0#1)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                          ()))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          (decode_aarch32_instrs_VMSR_A1enc_AS_txt
                                                                                                                                                                                            cond
                                                                                                                                                                                            reg
                                                                                                                                                                                            Rt)))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__134 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 31
                                                                                                                                                                                                 23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   21
                                                                                                                                                                                                   18)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     11
                                                                                                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       6
                                                                                                                                                                                                       6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       4
                                                                                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__133 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__133 <b 3868) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__134 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 3868
                                                                                                                                                                                          let D :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              22
                                                                                                                                                                                              1)
                                                                                                                                                                                          let RM :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              16
                                                                                                                                                                                              2)
                                                                                                                                                                                          let Vd :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              12
                                                                                                                                                                                              4)
                                                                                                                                                                                          let size :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              8
                                                                                                                                                                                              2)
                                                                                                                                                                                          let op :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              7
                                                                                                                                                                                              1)
                                                                                                                                                                                          let M :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              5
                                                                                                                                                                                              1)
                                                                                                                                                                                          let Vm :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              0
                                                                                                                                                                                              4)
                                                                                                                                                                                          (decode_aarch32_instrs_VCVTA_vfp_A1enc_A_txt
                                                                                                                                                                                            D
                                                                                                                                                                                            RM
                                                                                                                                                                                            Vd
                                                                                                                                                                                            size
                                                                                                                                                                                            op
                                                                                                                                                                                            M
                                                                                                                                                                                            Vm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__136 ← (( do
                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     31
                                                                                                                                                                                                     23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       21
                                                                                                                                                                                                       20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         11
                                                                                                                                                                                                         10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         4
                                                                                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__135 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__135 <b 3871) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__136 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 3871
                                                                                                                                                                                              let D :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  22
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let Vn :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  16
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Vd :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  12
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let size :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  8
                                                                                                                                                                                                  2)
                                                                                                                                                                                              let N :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  7
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let op :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  6
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let M :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  5
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let Vm :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  0
                                                                                                                                                                                                  4)
                                                                                                                                                                                              (decode_aarch32_instrs_VMAXNM_A2enc_A_txt
                                                                                                                                                                                                D
                                                                                                                                                                                                Vn
                                                                                                                                                                                                Vd
                                                                                                                                                                                                size
                                                                                                                                                                                                N
                                                                                                                                                                                                op
                                                                                                                                                                                                M
                                                                                                                                                                                                Vm))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__138 ← (( do
                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         31
                                                                                                                                                                                                         23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                           21
                                                                                                                                                                                                           18)) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             11
                                                                                                                                                                                                             10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               7
                                                                                                                                                                                                               6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               4
                                                                                                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__137 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__137 <b 3876) : Bool))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                )
                                                                                                                                                                                                :
                                                                                                                                                                                                SailM
                                                                                                                                                                                                Bool
                                                                                                                                                                                                )
                                                                                                                                                                                              if (w__138 : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 3876
                                                                                                                                                                                                  let D :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      22
                                                                                                                                                                                                      1)
                                                                                                                                                                                                  let RM :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      16
                                                                                                                                                                                                      2)
                                                                                                                                                                                                  let Vd :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      12
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let size :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      8
                                                                                                                                                                                                      2)
                                                                                                                                                                                                  let M :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      5
                                                                                                                                                                                                      1)
                                                                                                                                                                                                  let Vm :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      0
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  (decode_aarch32_instrs_VRINTA_vfp_A1enc_A_txt
                                                                                                                                                                                                    D
                                                                                                                                                                                                    RM
                                                                                                                                                                                                    Vd
                                                                                                                                                                                                    size
                                                                                                                                                                                                    M
                                                                                                                                                                                                    Vm))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let w__141 ← (( do
                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             27
                                                                                                                                                                                                             23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               21
                                                                                                                                                                                                               16)) == (0b110111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 11
                                                                                                                                                                                                                 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                   7
                                                                                                                                                                                                                   6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                   4
                                                                                                                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               28
                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__139 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__139 <b 3880) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    :
                                                                                                                                                                                                    SailM
                                                                                                                                                                                                    Bool
                                                                                                                                                                                                    )
                                                                                                                                                                                                  if (w__141 : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 3880
                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          28
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          22
                                                                                                                                                                                                          1)
                                                                                                                                                                                                      let Vd :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          12
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      let size :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          8
                                                                                                                                                                                                          2)
                                                                                                                                                                                                      let M :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          5
                                                                                                                                                                                                          1)
                                                                                                                                                                                                      let Vm :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          0
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      (decode_aarch32_instrs_VRINTX_vfp_A1enc_A_txt
                                                                                                                                                                                                        cond
                                                                                                                                                                                                        D
                                                                                                                                                                                                        Vd
                                                                                                                                                                                                        size
                                                                                                                                                                                                        M
                                                                                                                                                                                                        Vm))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let w__144 ← (( do
                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 27
                                                                                                                                                                                                                 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                   21
                                                                                                                                                                                                                   16)) == (0b110110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     11
                                                                                                                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       6
                                                                                                                                                                                                                       6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       4
                                                                                                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                   28
                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let w__142 ← (( do
                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                  :
                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                (pure (((w__142 <b 3884) : Bool))))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                        )
                                                                                                                                                                                                        :
                                                                                                                                                                                                        SailM
                                                                                                                                                                                                        Bool
                                                                                                                                                                                                        )
                                                                                                                                                                                                      if (w__144 : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 3884
                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              28
                                                                                                                                                                                                              4)
                                                                                                                                                                                                          let D :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              22
                                                                                                                                                                                                              1)
                                                                                                                                                                                                          let Vd :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              12
                                                                                                                                                                                                              4)
                                                                                                                                                                                                          let size :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              8
                                                                                                                                                                                                              2)
                                                                                                                                                                                                          let op :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              7
                                                                                                                                                                                                              1)
                                                                                                                                                                                                          let M :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              5
                                                                                                                                                                                                              1)
                                                                                                                                                                                                          let Vm :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              0
                                                                                                                                                                                                              4)
                                                                                                                                                                                                          (decode_aarch32_instrs_VRINTZ_vfp_A1enc_A_txt
                                                                                                                                                                                                            cond
                                                                                                                                                                                                            D
                                                                                                                                                                                                            Vd
                                                                                                                                                                                                            size
                                                                                                                                                                                                            op
                                                                                                                                                                                                            M
                                                                                                                                                                                                            Vm))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let w__146 ← (( do
                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     31
                                                                                                                                                                                                                     23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       11
                                                                                                                                                                                                                       10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         6
                                                                                                                                                                                                                         6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         4
                                                                                                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let w__145 ← (( do
                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                  :
                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                (pure (((w__145 <b 3886) : Bool))))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                            )
                                                                                                                                                                                                            :
                                                                                                                                                                                                            SailM
                                                                                                                                                                                                            Bool
                                                                                                                                                                                                            )
                                                                                                                                                                                                          if (w__146 : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 3886
                                                                                                                                                                                                              let D :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  22
                                                                                                                                                                                                                  1)
                                                                                                                                                                                                              let cc :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  20
                                                                                                                                                                                                                  2)
                                                                                                                                                                                                              let Vn :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  16
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let Vd :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  12
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let size :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  8
                                                                                                                                                                                                                  2)
                                                                                                                                                                                                              let N :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  7
                                                                                                                                                                                                                  1)
                                                                                                                                                                                                              let M :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  5
                                                                                                                                                                                                                  1)
                                                                                                                                                                                                              let Vm :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  0
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              (decode_aarch32_instrs_VSEL_A1enc_A_txt
                                                                                                                                                                                                                D
                                                                                                                                                                                                                cc
                                                                                                                                                                                                                Vn
                                                                                                                                                                                                                Vd
                                                                                                                                                                                                                size
                                                                                                                                                                                                                N
                                                                                                                                                                                                                M
                                                                                                                                                                                                                Vm))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              let w__148 ← (( do
                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         31
                                                                                                                                                                                                                         23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           21
                                                                                                                                                                                                                           20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           11
                                                                                                                                                                                                                           8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    let w__147 ← (( do
                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                      :
                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                    (pure (((w__147 <b 3900) : Bool))))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                )
                                                                                                                                                                                                                :
                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                )
                                                                                                                                                                                                              if (w__148 : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 3900
                                                                                                                                                                                                                  let D :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      22
                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                  let Vn :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      16
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  let Vd :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      12
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  let N :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      7
                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                  let Q :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      6
                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                  let M :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      5
                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                  let U :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      4
                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                  let Vm :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      0
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  (decode_aarch32_instrs_VDOT_A1enc_A_txt
                                                                                                                                                                                                                    D
                                                                                                                                                                                                                    Vn
                                                                                                                                                                                                                    Vd
                                                                                                                                                                                                                    N
                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                    M
                                                                                                                                                                                                                    U
                                                                                                                                                                                                                    Vm))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  let w__150 ← (( do
                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                             31
                                                                                                                                                                                                                             23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               21
                                                                                                                                                                                                                               20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               11
                                                                                                                                                                                                                               8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        let w__149 ← (( do
                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                          :
                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                        (pure (((w__149 <b 3902) : Bool))))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                    :
                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                  if (w__150 : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 3902
                                                                                                                                                                                                                      let op1 :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          23
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          22
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      let op2 :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          20
                                                                                                                                                                                                                          2)
                                                                                                                                                                                                                      let Vn :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          16
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      let Vd :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          12
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      let N :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          7
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      let Q :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          6
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      let M :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          5
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      let U :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          4
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      let Vm :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          0
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      (decode_aarch32_instrs_VDOT_s_A1enc_A_txt
                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                        D
                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                        Vn
                                                                                                                                                                                                                        Vd
                                                                                                                                                                                                                        N
                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                        M
                                                                                                                                                                                                                        U
                                                                                                                                                                                                                        Vm))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      let w__153 ← (( do
                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                 23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                   21
                                                                                                                                                                                                                                   16)) == (0b111001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                     6)) == (0b101111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     4
                                                                                                                                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let w__151 ← (( do
                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                (pure (((w__151 <b 3904) : Bool))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                        :
                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                      if (w__153 : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 3904
                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              28
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          let D :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              22
                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                          let Vd :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              12
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          let M :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              5
                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                          let Vm :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              0
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          (decode_aarch32_instrs_VJCVT_A1enc_A_txt
                                                                                                                                                                                                                            cond
                                                                                                                                                                                                                            D
                                                                                                                                                                                                                            Vd
                                                                                                                                                                                                                            M
                                                                                                                                                                                                                            Vm))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          let w__155 ← (( do
                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     31
                                                                                                                                                                                                                                     25)) == (0b1111110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                       21
                                                                                                                                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                         8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         4
                                                                                                                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let w__154 ← (( do
                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                (pure (((w__154 <b 3906) : Bool))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                            :
                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                          if (w__155 : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 3906
                                                                                                                                                                                                                              let rot :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  23
                                                                                                                                                                                                                                  2)
                                                                                                                                                                                                                              let D :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  22
                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                              let S :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  20
                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                              let Vn :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              let Vd :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              let N :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  7
                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                              let Q :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  6
                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                              let M :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  5
                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                              let Vm :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              (decode_aarch32_instrs_VCMLA_A1enc_A_txt
                                                                                                                                                                                                                                rot
                                                                                                                                                                                                                                D
                                                                                                                                                                                                                                S
                                                                                                                                                                                                                                Vn
                                                                                                                                                                                                                                Vd
                                                                                                                                                                                                                                N
                                                                                                                                                                                                                                Q
                                                                                                                                                                                                                                M
                                                                                                                                                                                                                                Vm))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              let w__157 ← (( do
                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                         24)) == (0xFE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                           8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    let w__156 ← (( do
                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                    (pure (((w__156 <b 3908) : Bool))))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                              if (w__157 : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 3908
                                                                                                                                                                                                                                  let S :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      23
                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                  let D :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      22
                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                  let rot :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      20
                                                                                                                                                                                                                                      2)
                                                                                                                                                                                                                                  let Vn :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  let Vd :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  let N :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      7
                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                  let Q :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      6
                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                  let M :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                  let Vm :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  (decode_aarch32_instrs_VCMLA_idx_A1enc_A_txt
                                                                                                                                                                                                                                    S
                                                                                                                                                                                                                                    D
                                                                                                                                                                                                                                    rot
                                                                                                                                                                                                                                    Vn
                                                                                                                                                                                                                                    Vd
                                                                                                                                                                                                                                    N
                                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                                    M
                                                                                                                                                                                                                                    Vm))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  let w__159 ← (( do
                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                             25)) == (0b1111110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                               23
                                                                                                                                                                                                                                               23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 21
                                                                                                                                                                                                                                                 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                   11
                                                                                                                                                                                                                                                   8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                   4
                                                                                                                                                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        let w__158 ← (( do
                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                        (pure (((w__158 <b 3910) : Bool))))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                  if (w__159 : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 3910
                                                                                                                                                                                                                                      let rot :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          24
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          22
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      let S :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          20
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      let Vn :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let Vd :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let N :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          7
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      let Q :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          6
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      let M :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      let Vm :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      (decode_aarch32_instrs_VCADD_A1enc_A_txt
                                                                                                                                                                                                                                        rot
                                                                                                                                                                                                                                        D
                                                                                                                                                                                                                                        S
                                                                                                                                                                                                                                        Vn
                                                                                                                                                                                                                                        Vd
                                                                                                                                                                                                                                        N
                                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                                        M
                                                                                                                                                                                                                                        Vm))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      let w__161 ← (( do
                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 31
                                                                                                                                                                                                                                                 24)) == (0xFC#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                   21
                                                                                                                                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                     8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     4
                                                                                                                                                                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            let w__160 ← (( do
                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                            (pure (((w__160 <b 3912) : Bool))))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                      if (w__161 : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 3912
                                                                                                                                                                                                                                          let S :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              23
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          let D :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              22
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          let Vn :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let Vd :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let N :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              7
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          let Q :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              6
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          let M :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              5
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          let Vm :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          (decode_aarch32_instrs_VFMAL_A1enc_A_txt
                                                                                                                                                                                                                                            S
                                                                                                                                                                                                                                            D
                                                                                                                                                                                                                                            Vn
                                                                                                                                                                                                                                            Vd
                                                                                                                                                                                                                                            N
                                                                                                                                                                                                                                            Q
                                                                                                                                                                                                                                            M
                                                                                                                                                                                                                                            Vm))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          let w__163 ← (( do
                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     31
                                                                                                                                                                                                                                                     23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       21
                                                                                                                                                                                                                                                       21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                         8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         4
                                                                                                                                                                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                let w__162 ← (( do
                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                (pure (((w__162 <b 3914) : Bool))))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                          if (w__163 : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 3914
                                                                                                                                                                                                                                              let D :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  22
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              let S :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  20
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              let Vn :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let Vd :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let N :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  7
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              let Q :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  6
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              let M :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  5
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              let Vm :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              (decode_aarch32_instrs_VFMAL_i_A1enc_A_txt
                                                                                                                                                                                                                                                D
                                                                                                                                                                                                                                                S
                                                                                                                                                                                                                                                Vn
                                                                                                                                                                                                                                                Vd
                                                                                                                                                                                                                                                N
                                                                                                                                                                                                                                                Q
                                                                                                                                                                                                                                                M
                                                                                                                                                                                                                                                Vm))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              let w__165 ← (( do
                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                                         23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           21
                                                                                                                                                                                                                                                           20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                             8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             4
                                                                                                                                                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    let w__164 ← (( do
                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                    (pure (((w__164 <b 3916) : Bool))))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                              if (w__165 : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 3916
                                                                                                                                                                                                                                                  let D :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      22
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  let Vn :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  let Vd :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  let N :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      7
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  let Q :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      6
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  let M :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  let Vm :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  (decode_aarch32_instrs_VDOT_bf16_A1enc_A_txt
                                                                                                                                                                                                                                                    D
                                                                                                                                                                                                                                                    Vn
                                                                                                                                                                                                                                                    Vd
                                                                                                                                                                                                                                                    N
                                                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                                                    M
                                                                                                                                                                                                                                                    Vm))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  let w__167 ← (( do
                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                                             23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                               21
                                                                                                                                                                                                                                                               20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 4
                                                                                                                                                                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        let w__166 ← (( do
                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                        (pure (((w__166 <b 3918) : Bool))))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                  if (w__167 : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 3918
                                                                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          22
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      let Vn :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      let Vd :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      let N :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          7
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      let Q :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          6
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      let M :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      let Vm :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      (decode_aarch32_instrs_VDOT_bf16_i_A1enc_A_txt
                                                                                                                                                                                                                                                        D
                                                                                                                                                                                                                                                        Vn
                                                                                                                                                                                                                                                        Vd
                                                                                                                                                                                                                                                        N
                                                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                                                        M
                                                                                                                                                                                                                                                        Vm))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      let w__169 ← (( do
                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 31
                                                                                                                                                                                                                                                                 23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                   21
                                                                                                                                                                                                                                                                   20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                                     8)) == (0xC#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       6
                                                                                                                                                                                                                                                                       6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       4
                                                                                                                                                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            let w__168 ← (( do
                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                            (pure (((w__168 <b 3920) : Bool))))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                      if (w__169 : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 3920
                                                                                                                                                                                                                                                          let D :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              22
                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                          let Vn :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          let Vd :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          let N :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              7
                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                          let M :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              5
                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                          let Vm :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          (decode_aarch32_instrs_VMMLA_A1enc_A_txt
                                                                                                                                                                                                                                                            D
                                                                                                                                                                                                                                                            Vn
                                                                                                                                                                                                                                                            Vd
                                                                                                                                                                                                                                                            N
                                                                                                                                                                                                                                                            M
                                                                                                                                                                                                                                                            Vm))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          let w__172 ← (( do
                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                                                     23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       21
                                                                                                                                                                                                                                                                       16)) == (0b110011#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                                         6)) == (0b100101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         4
                                                                                                                                                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    let w__170 ← (( do
                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                    (pure (((w__170 <b 3924) : Bool))))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                          if (w__172 : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 3924
                                                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              let D :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  22
                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                              let Vd :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              let M :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  5
                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                              let Vm :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              (decode_aarch32_instrs_VCVTB_bf16_A1enc_A_txt
                                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                                D
                                                                                                                                                                                                                                                                Vd
                                                                                                                                                                                                                                                                M
                                                                                                                                                                                                                                                                Vm))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              let w__175 ← (( do
                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                                                         23)) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           21
                                                                                                                                                                                                                                                                           16)) == (0b110011#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                                             6)) == (0b100111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             4
                                                                                                                                                                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let w__173 ← (( do
                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                        (pure (((w__173 <b 3926) : Bool))))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                              if (w__175 : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 3926
                                                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  let D :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      22
                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                  let Vd :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  let M :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                  let Vm :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_VCVTT_A1enc_A_txt
                                                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                                                    D
                                                                                                                                                                                                                                                                    Vd
                                                                                                                                                                                                                                                                    M
                                                                                                                                                                                                                                                                    Vm))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  let w__177 ← (( do
                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                                                             23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                               21
                                                                                                                                                                                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                                 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 4
                                                                                                                                                                                                                                                                                 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let w__176 ← (( do
                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                        (pure (((w__176 <b 3928) : Bool))))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                  if (w__177 : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 3928
                                                                                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          22
                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                      let Vn :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      let Vd :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      let N :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          7
                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                      let Q :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          6
                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                      let M :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                      let Vm :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_VFMA_bf_A1enc_A_txt
                                                                                                                                                                                                                                                                        D
                                                                                                                                                                                                                                                                        Vn
                                                                                                                                                                                                                                                                        Vd
                                                                                                                                                                                                                                                                        N
                                                                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                                                                        M
                                                                                                                                                                                                                                                                        Vm))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      let w__179 ← (( do
                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 31
                                                                                                                                                                                                                                                                                 23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                   21
                                                                                                                                                                                                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                                                     8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     4
                                                                                                                                                                                                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            let w__178 ← (( do
                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                            (pure (((w__178 <b 3930) : Bool))))
                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                      if (w__179 : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 3930
                                                                                                                                                                                                                                                                          let D :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              22
                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                          let Vn :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          let Vd :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          let N :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              7
                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                          let Q :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              6
                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                          let M :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              5
                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                          let Vm :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_VFMA_bfs_A1enc_A_txt
                                                                                                                                                                                                                                                                            D
                                                                                                                                                                                                                                                                            Vn
                                                                                                                                                                                                                                                                            Vd
                                                                                                                                                                                                                                                                            N
                                                                                                                                                                                                                                                                            Q
                                                                                                                                                                                                                                                                            M
                                                                                                                                                                                                                                                                            Vm))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          let w__181 ← (( do
                                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     31
                                                                                                                                                                                                                                                                                     24)) == (0xFC#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                       21
                                                                                                                                                                                                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                                                         8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         6
                                                                                                                                                                                                                                                                                         6)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                let w__180 ← (( do
                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                (pure (((w__180 <b 3932) : Bool))))
                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                          if (w__181 : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 3932
                                                                                                                                                                                                                                                                              let B :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  23
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              let D :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  22
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              let Vn :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                              let Vd :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                              let N :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  7
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              let M :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  5
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              let U :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  4
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              let Vm :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_MMLA_A1enc_A_txt
                                                                                                                                                                                                                                                                                B
                                                                                                                                                                                                                                                                                D
                                                                                                                                                                                                                                                                                Vn
                                                                                                                                                                                                                                                                                Vd
                                                                                                                                                                                                                                                                                N
                                                                                                                                                                                                                                                                                M
                                                                                                                                                                                                                                                                                U
                                                                                                                                                                                                                                                                                Vm))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              let w__183 ← (( do
                                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                                                                         23)) == (0b111111001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                           21
                                                                                                                                                                                                                                                                                           20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                                                             8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             4
                                                                                                                                                                                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                    let w__182 ← (( do
                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                    (pure (((w__182 <b 3934) : Bool))))
                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                              if (w__183 : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 3934
                                                                                                                                                                                                                                                                                  let D :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      22
                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                  let Vn :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  let Vd :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  let N :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      7
                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                  let Q :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      6
                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                  let M :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                  let Vm :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_VUSDOT_A1enc_A_txt
                                                                                                                                                                                                                                                                                    D
                                                                                                                                                                                                                                                                                    Vn
                                                                                                                                                                                                                                                                                    Vd
                                                                                                                                                                                                                                                                                    N
                                                                                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                                                                                    M
                                                                                                                                                                                                                                                                                    Vm))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  let w__185 ← (( do
                                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                                                                             23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               21
                                                                                                                                                                                                                                                                                               20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                                                                               8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                        let w__184 ← (( do
                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                        (pure (((w__184 <b 3936) : Bool))))
                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                  if (w__185 : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 3936
                                                                                                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          22
                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                      let Vn :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      let Vd :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      let N :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          7
                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                      let Q :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          6
                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                      let M :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                      let U :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                      let Vm :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_DOT_A1enc_A_txt
                                                                                                                                                                                                                                                                                        D
                                                                                                                                                                                                                                                                                        Vn
                                                                                                                                                                                                                                                                                        Vd
                                                                                                                                                                                                                                                                                        N
                                                                                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                                                                                        M
                                                                                                                                                                                                                                                                                        U
                                                                                                                                                                                                                                                                                        Vm))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    sailThrow ((Error_Undefined
                                                                                                                                                                                                                                                                                      ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
