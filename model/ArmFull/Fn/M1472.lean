import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0192
import ArmFull.Fn.M0202
import ArmFull.Fn.M0229
import ArmFull.Fn.M0246
import ArmFull.Fn.M0837
import ArmFull.Fn.M0838
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

/-- Type quantifiers: pc : Int -/
def __DecodeT32__seg0 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1 ← (( do
    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
               __opcode 25 21)) == (0b01010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 2814) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 2814
      let i := (BitVec.slice __opcode 26 1)
      let S := (BitVec.slice __opcode 20 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let imm3 := (BitVec.slice __opcode 12 3)
      let Rd := (BitVec.slice __opcode 8 4)
      let imm8 := (BitVec.slice __opcode 0 8)
      (decode_aarch32_instrs_ADC_i_T1enc_A_txt i S Rn imm3 Rd imm8)
      (pure false))
  else
    (do
      let w__3 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11101011010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 2817) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 2817
          let S := (BitVec.slice __opcode 20 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let imm3 := (BitVec.slice __opcode 12 3)
          let Rd := (BitVec.slice __opcode 8 4)
          let imm2 := (BitVec.slice __opcode 6 2)
          let stype := (BitVec.slice __opcode 4 2)
          let Rm := (BitVec.slice __opcode 0 4)
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 15)])) != 0#1) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_aarch32_instrs_ADC_r_T2enc_A_txt S Rn imm3 Rd imm2 stype Rm))
          (pure false))
      else
        (do
          let w__5 ← (( do
            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                       __opcode 25 21)) == (0b01000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 2822) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 2822
              let i := (BitVec.slice __opcode 26 1)
              let S := (BitVec.slice __opcode 20 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let imm3 := (BitVec.slice __opcode 12 3)
              let Rd := (BitVec.slice __opcode 8 4)
              let imm8 := (BitVec.slice __opcode 0 8)
              (decode_aarch32_instrs_ADD_i_T3enc_A_txt i S Rn imm3 Rd imm8)
              (pure false))
          else
            (do
              let w__7 ← (( do
                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 25 20)) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 2823) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 2823
                  let i := (BitVec.slice __opcode 26 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let imm3 := (BitVec.slice __opcode 12 3)
                  let Rd := (BitVec.slice __opcode 8 4)
                  let imm8 := (BitVec.slice __opcode 0 8)
                  (decode_aarch32_instrs_ADD_i_T4enc_A_txt i Rn imm3 Rd imm8)
                  (pure false))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11101011000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 2827) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 2827
                      let S := (BitVec.slice __opcode 20 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let imm3 := (BitVec.slice __opcode 12 3)
                      let Rd := (BitVec.slice __opcode 8 4)
                      let imm2 := (BitVec.slice __opcode 6 2)
                      let stype := (BitVec.slice __opcode 4 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 15)])) != 0#1) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_ADD_r_T3enc_A_txt S Rn imm3 Rd imm2 stype Rm))
                      (pure false))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31
                                 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                   __opcode 25 21)) == (0b01000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                   __opcode 19 15)) == (0b11010#5 : (BitVec 5))))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 2832) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 2832
                          let i := (BitVec.slice __opcode 26 1)
                          let S := (BitVec.slice __opcode 20 1)
                          let imm3 := (BitVec.slice __opcode 12 3)
                          let Rd := (BitVec.slice __opcode 8 4)
                          let imm8 := (BitVec.slice __opcode 0 8)
                          (decode_aarch32_instrs_ADD_SP_i_T3enc_A_txt i S imm3 Rd imm8)
                          (pure false))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode
                                     31 27)) == (0b11110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                     __opcode 25 15)) == (0b10000011010#11 : (BitVec 11)))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 2833) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 2833
                              let i := (BitVec.slice __opcode 26 1)
                              let imm3 := (BitVec.slice __opcode 12 3)
                              let Rd := (BitVec.slice __opcode 8 4)
                              let imm8 := (BitVec.slice __opcode 0 8)
                              (decode_aarch32_instrs_ADD_SP_i_T4enc_A_txt i imm3 Rd imm8)
                              (pure false))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11101011000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                         __opcode 19 15)) == (0b11010#5 : (BitVec 5)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 2837) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 2837
                                  let S := (BitVec.slice __opcode 20 1)
                                  let imm3 := (BitVec.slice __opcode 12 3)
                                  let Rd := (BitVec.slice __opcode 8 4)
                                  let imm2 := (BitVec.slice __opcode 6 2)
                                  let stype := (BitVec.slice __opcode 4 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 15)])) != 0#1) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_aarch32_instrs_ADD_SP_r_T3enc_A_txt S imm3 Rd imm2
                                        stype Rm))
                                  (pure false))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                             __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 25 15)) == (0b10101011110#11 : (BitVec 11)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 2841) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2841
                                      let i := (BitVec.slice __opcode 26 1)
                                      let imm3 := (BitVec.slice __opcode 12 3)
                                      let Rd := (BitVec.slice __opcode 8 4)
                                      let imm8 := (BitVec.slice __opcode 0 8)
                                      (decode_aarch32_instrs_ADR_T2enc_A_txt i imm3 Rd imm8)
                                      (pure false))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                 __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 25 15)) == (0b10000011110#11 : (BitVec 11)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 2842) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2842
                                          let i := (BitVec.slice __opcode 26 1)
                                          let imm3 := (BitVec.slice __opcode 12 3)
                                          let Rd := (BitVec.slice __opcode 8 4)
                                          let imm8 := (BitVec.slice __opcode 0 8)
                                          (decode_aarch32_instrs_ADR_T3enc_A_txt i imm3 Rd imm8)
                                          (pure false))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                     __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                       __opcode 25 21)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 2844) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2844
                                              let i := (BitVec.slice __opcode 26 1)
                                              let S := (BitVec.slice __opcode 20 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let imm3 := (BitVec.slice __opcode 12 3)
                                              let Rd := (BitVec.slice __opcode 8 4)
                                              let imm8 := (BitVec.slice __opcode 0 8)
                                              (decode_aarch32_instrs_AND_i_T1enc_A_txt i S Rn imm3
                                                Rd imm8)
                                              (pure false))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b11101010000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 2847) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2847
                                                  let S := (BitVec.slice __opcode 20 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let imm3 := (BitVec.slice __opcode 12 3)
                                                  let Rd := (BitVec.slice __opcode 8 4)
                                                  let imm2 := (BitVec.slice __opcode 6 2)
                                                  let stype := (BitVec.slice __opcode 4 2)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 15)])) != 0#1) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_AND_r_T2enc_A_txt S Rn
                                                        imm3 Rd imm2 stype Rm))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__26 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                             __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 15 14)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 12 12)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 22 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__24 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__24 <b 2854) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__26 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2854
                                                      let S := (BitVec.slice __opcode 26 1)
                                                      let cond := (BitVec.slice __opcode 22 4)
                                                      let imm6 := (BitVec.slice __opcode 16 6)
                                                      let J1 := (BitVec.slice __opcode 13 1)
                                                      let J2 := (BitVec.slice __opcode 11 1)
                                                      let imm11 := (BitVec.slice __opcode 0 11)
                                                      (decode_aarch32_instrs_B_T3enc_A_txt S cond
                                                        imm6 J1 J2 imm11)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__28 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                 __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 15 14)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 12 12)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__27 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__27 <b 2855) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__28 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2855
                                                          let S := (BitVec.slice __opcode 26 1)
                                                          let imm10 := (BitVec.slice __opcode 16 10)
                                                          let J1 := (BitVec.slice __opcode 13 1)
                                                          let J2 := (BitVec.slice __opcode 11 1)
                                                          let imm11 := (BitVec.slice __opcode 0 11)
                                                          (decode_aarch32_instrs_B_T4enc_A_txt S
                                                            imm10 J1 J2 imm11)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__30 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                     __opcode 31 15)) == (0b11110011011011110#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 5 5)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__29 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__29 <b 2857) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__30 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2857
                                                              let imm3 :=
                                                                (BitVec.slice __opcode 12 3)
                                                              let Rd := (BitVec.slice __opcode 8 4)
                                                              let imm2 :=
                                                                (BitVec.slice __opcode 6 2)
                                                              let msb := (BitVec.slice __opcode 0 5)
                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 5)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_BFC_T1enc_A_txt
                                                                    imm3 Rd imm2 msb))
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__32 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xF36#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 5 5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__31 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__31 <b 2859) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__32 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2859
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let imm3 :=
                                                                    (BitVec.slice __opcode 12 3)
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 8 4)
                                                                  let imm2 :=
                                                                    (BitVec.slice __opcode 6 2)
                                                                  let msb :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 5)])) != 0#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_BFI_T1enc_A_txt
                                                                        Rn imm3 Rd imm2 msb))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__34 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                             __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                               __opcode 25 21)) == (0b00001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__33 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__33 <b 2861) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__34 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2861
                                                                      let i :=
                                                                        (BitVec.slice __opcode 26 1)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 20 1)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let imm3 :=
                                                                        (BitVec.slice __opcode 12 3)
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 8 4)
                                                                      let imm8 :=
                                                                        (BitVec.slice __opcode 0 8)
                                                                      (decode_aarch32_instrs_BIC_i_T1enc_A_txt
                                                                        i S Rn imm3 Rd imm8)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__36 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b11101010001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__35 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__35 <b 2864) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__36 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2864
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let imm3 :=
                                                                            (BitVec.slice __opcode
                                                                              12 3)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          let imm2 :=
                                                                            (BitVec.slice __opcode 6
                                                                              2)
                                                                          let stype :=
                                                                            (BitVec.slice __opcode 4
                                                                              2)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 15)])) != 0#1) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_BIC_r_T2enc_A_txt
                                                                                S Rn imm3 Rd imm2
                                                                                stype Rm))
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__38 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       14)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 12
                                                                                       12)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__37 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__37 <b 2870) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__38 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2870
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 26 1)
                                                                              let imm10 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 10)
                                                                              let J1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 1)
                                                                              let J2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 11 1)
                                                                              let imm11 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 11)
                                                                              (decode_aarch32_instrs_BL_i_T1enc_A_txt
                                                                                S imm10 J1 J2 imm11)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__40 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 14)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           12 12)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__39 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__39 <b 2871) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__40 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2871
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 26 1)
                                                                                  let imm10H :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 10)
                                                                                  let J1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 1)
                                                                                  let J2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let imm10L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 1 10)
                                                                                  let H :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 1)
                                                                                  (decode_aarch32_instrs_BL_i_T2enc_A_txt
                                                                                    S imm10H J1 J2
                                                                                    imm10L H)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__42 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xF3C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 0)) == (0x8F00#16 : (BitVec 16)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__41 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__41 <b 2877) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__42 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2877
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      if (((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       13)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 7)])) != 0#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_aarch32_instrs_BXJ_T1enc_A_txt
                                                                                            Rm))
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__44 ← (( do
                                                                                        if (((__opcode == 0b11110011101111111000111100101111#32) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__43 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__43 <b 2880) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__44 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2880
                                                                                          if (((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     3)])) != 1#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_aarch32_instrs_CLREX_T1enc_A_txt
                                                                                                ()))
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__46 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xFAB#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       7
                                                                                                       4)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__45 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__45 <b 2882) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__46 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2882
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_CLZ_T1enc_A_txt
                                                                                                Rn
                                                                                                Rd
                                                                                                Rm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__48 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           25
                                                                                                           20)) == (0b010001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             8)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__47 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__47 <b 2884) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__48 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2884
                                                                                                  let i :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      26
                                                                                                      1)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let imm3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      3)
                                                                                                  let imm8 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      8)
                                                                                                  (decode_aarch32_instrs_CMN_i_T1enc_A_txt
                                                                                                    i
                                                                                                    Rn
                                                                                                    imm3
                                                                                                    imm8)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__50 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xEB1#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               8)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__49 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__49 <b 2887) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__50 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2887
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let imm3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          3)
                                                                                                      let imm2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          2)
                                                                                                      let stype :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          2)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               15)])) != 0#1) : Bool)
                                                                                                      then
                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                          ()))
                                                                                                      else
                                                                                                        (do
                                                                                                          (decode_aarch32_instrs_CMN_r_T2enc_A_txt
                                                                                                            Rn
                                                                                                            imm3
                                                                                                            imm2
                                                                                                            stype
                                                                                                            Rm))
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__52 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   25
                                                                                                                   20)) == (0b011011#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     8)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__51 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__51 <b 2891) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__52 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2891
                                                                                                          let i :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              26
                                                                                                              1)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let imm3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              3)
                                                                                                          let imm8 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              8)
                                                                                                          (decode_aarch32_instrs_CMP_i_T2enc_A_txt
                                                                                                            i
                                                                                                            Rn
                                                                                                            imm3
                                                                                                            imm8)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__54 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xEBB#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       8)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__53 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__53 <b 2895) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__54 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2895
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let imm3 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  3)
                                                                                                              let imm2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  6
                                                                                                                  2)
                                                                                                              let stype :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  2)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       15)])) != 0#1) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_aarch32_instrs_CMP_r_T3enc_A_txt
                                                                                                                    Rn
                                                                                                                    imm3
                                                                                                                    imm2
                                                                                                                    stype
                                                                                                                    Rm))
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__56 ← (( do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       31
                                                                                                                       4)) == (0xF3AF80F#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__55 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__55 <b 2898) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__56 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2898
                                                                                                                  let option_name :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             11)])) != 0#1)) : Bool)
                                                                                                                  then
                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                      ()))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      (decode_aarch32_instrs_DBG_T1enc_A_txt
                                                                                                                        option_name))
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__58 ← (( do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           31
                                                                                                                           4)) == (0xF3BF8F5#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__57 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__57 <b 2900) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__58 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2900
                                                                                                                      let option_name :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                      then
                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                          ()))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          (decode_aarch32_instrs_DMB_T1enc_A_txt
                                                                                                                            option_name))
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__60 ← (( do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               31
                                                                                                                               4)) == (0xF3BF8F4#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__59 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__59 <b 2902) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__60 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2902
                                                                                                                          let option_name :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                          then
                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                              ()))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              (decode_aarch32_instrs_DSB_T1enc_A_txt
                                                                                                                                option_name))
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__62 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       25
                                                                                                                                       21)) == (0b00100#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__61 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__61 <b 2904) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__62 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2904
                                                                                                                              let i :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  26
                                                                                                                                  1)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  20
                                                                                                                                  1)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let imm3 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  3)
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  4)
                                                                                                                              let imm8 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  8)
                                                                                                                              (decode_aarch32_instrs_EOR_i_T1enc_A_txt
                                                                                                                                i
                                                                                                                                S
                                                                                                                                Rn
                                                                                                                                imm3
                                                                                                                                Rd
                                                                                                                                imm8)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__64 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b11101010100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__63 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__63 <b 2907) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__64 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2907
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      20
                                                                                                                                      1)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let imm3 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      3)
                                                                                                                                  let Rd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      8
                                                                                                                                      4)
                                                                                                                                  let imm2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      2)
                                                                                                                                  let stype :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      2)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           15)])) != 0#1) : Bool)
                                                                                                                                  then
                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                      ()))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      (decode_aarch32_instrs_EOR_r_T2enc_A_txt
                                                                                                                                        S
                                                                                                                                        Rn
                                                                                                                                        imm3
                                                                                                                                        Rd
                                                                                                                                        imm2
                                                                                                                                        stype
                                                                                                                                        Rm))
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__66 ← (( do
                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           31
                                                                                                                                           4)) == (0xF3BF8F6#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__65 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__65 <b 2910) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__66 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2910
                                                                                                                                      let option_name :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                               __opcode
                                                                                                                                                               16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                               __opcode
                                                                                                                                                               17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                             __opcode
                                                                                                                                                             18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                           __opcode
                                                                                                                                                           19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                         __opcode
                                                                                                                                                         13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                       __opcode
                                                                                                                                                       8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                                      then
                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                          ()))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          (decode_aarch32_instrs_ISB_T1enc_A_txt
                                                                                                                                            option_name))
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__68 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   22
                                                                                                                                                   22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     20
                                                                                                                                                     20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     8)) == (0x5E#8 : (BitVec 8)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__67 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__67 <b 2913) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__68 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2913
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
                                                                                                                                          let imm8 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              8)
                                                                                                                                          (decode_aarch32_instrs_LDC_i_T1enc_A_txt
                                                                                                                                            P
                                                                                                                                            U
                                                                                                                                            W
                                                                                                                                            Rn
                                                                                                                                            imm8)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__70 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       22
                                                                                                                                                       22)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       20
                                                                                                                                                       8)) == (0b1111101011110#13 : (BitVec 13))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__69 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__69 <b 2915) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__70 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2915
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
                                                                                                                                              let W :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  21
                                                                                                                                                  1)
                                                                                                                                              let imm8 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  8)
                                                                                                                                              (decode_aarch32_instrs_LDC_l_T1enc_A_txt
                                                                                                                                                P
                                                                                                                                                U
                                                                                                                                                W
                                                                                                                                                imm8)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))


end ArmFull.Functions
