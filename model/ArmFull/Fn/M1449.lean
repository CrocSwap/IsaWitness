import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0179
import ArmFull.Fn.M0214
import ArmFull.Fn.M0229
import ArmFull.Fn.M0230
import ArmFull.Fn.M0231
import ArmFull.Fn.M0234
import ArmFull.Fn.M0236
import ArmFull.Fn.M0240
import ArmFull.Fn.M0246
import ArmFull.Fn.M0248
import ArmFull.Fn.M0837
import ArmFull.Fn.M0838
import ArmFull.Fn.M0839
import ArmFull.Fn.M0842
import ArmFull.Fn.M0853
import ArmFull.Fn.M0928
import ArmFull.Fn.M1143
import ArmFull.Fn.M1280
import ArmFull.Fn.M1281
import ArmFull.Fn.M1282
import ArmFull.Fn.M1283
import ArmFull.Fn.M1284

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
def __DecodeT16 (pc : Int) (__opcode : (BitVec 16)) : SailM Unit := do
  let w__1 ← (( do
    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 15 6)) == (0b0100000101#10 : (BitVec 10))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 2816) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 2816
      let Rm := (BitVec.slice __opcode 3 3)
      let Rdn := (BitVec.slice __opcode 0 3)
      (decode_aarch32_instrs_ADC_r_T1enc_A_txt Rm Rdn))
  else
    (do
      let w__3 ← (( do
        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 15 9)) == (0b0001110#7 : (BitVec 7))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 2820) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 2820
          let imm3 := (BitVec.slice __opcode 6 3)
          let Rn := (BitVec.slice __opcode 3 3)
          let Rd := (BitVec.slice __opcode 0 3)
          (decode_aarch32_instrs_ADD_i_T1enc_A_txt imm3 Rn Rd))
      else
        (do
          let w__5 ← (( do
            if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 15 11)) == (0b00110#5 : (BitVec 5))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 2821) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 2821
              let Rdn := (BitVec.slice __opcode 8 3)
              let imm8 := (BitVec.slice __opcode 0 8)
              (decode_aarch32_instrs_ADD_i_T2enc_A_txt Rdn imm8))
          else
            (do
              let w__7 ← (( do
                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 15 9)) == (0b0001100#7 : (BitVec 7))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 2825) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 2825
                  let Rm := (BitVec.slice __opcode 6 3)
                  let Rn := (BitVec.slice __opcode 3 3)
                  let Rd := (BitVec.slice __opcode 0 3)
                  (decode_aarch32_instrs_ADD_r_T1enc_A_txt Rm Rn Rd))
              else
                (do
                  let w__9 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 15 8)) == (0x44#8 : (BitVec 8))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 2826) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 2826
                      let DN := (BitVec.slice __opcode 7 1)
                      let Rm := (BitVec.slice __opcode 3 4)
                      let Rdn := (BitVec.slice __opcode 0 3)
                      (decode_aarch32_instrs_ADD_r_T2enc_A_txt DN Rm Rdn))
                  else
                    (do
                      let w__11 ← (( do
                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 15 11)) == (0b10101#5 : (BitVec 5))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 2830) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 2830
                          let Rd := (BitVec.slice __opcode 8 3)
                          let imm8 := (BitVec.slice __opcode 0 8)
                          (decode_aarch32_instrs_ADD_SP_i_T1enc_A_txt Rd imm8))
                      else
                        (do
                          let w__13 ← (( do
                            if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                   15 7)) == (0b101100000#9 : (BitVec 9))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 2831) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 2831
                              let imm7 := (BitVec.slice __opcode 0 7)
                              (decode_aarch32_instrs_ADD_SP_i_T2enc_A_txt imm7))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 15 8)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 6 3)) == (0xD#4 : (BitVec 4)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 2835) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 2835
                                  let DM := (BitVec.slice __opcode 7 1)
                                  let Rdm := (BitVec.slice __opcode 0 3)
                                  (decode_aarch32_instrs_ADD_SP_r_T1enc_A_txt DM Rdm))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 15 7)) == (0b010001001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 2 0)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 2836) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2836
                                      let Rm := (BitVec.slice __opcode 3 4)
                                      (decode_aarch32_instrs_ADD_SP_r_T2enc_A_txt Rm))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                               __opcode 15 11)) == (0b10100#5 : (BitVec 5))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 2840) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2840
                                          let Rd := (BitVec.slice __opcode 8 3)
                                          let imm8 := (BitVec.slice __opcode 0 8)
                                          (decode_aarch32_instrs_ADR_T1enc_A_txt Rd imm8))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                   __opcode 15 6)) == (0b0100000000#10 : (BitVec 10))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 2846) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2846
                                              let Rm := (BitVec.slice __opcode 3 3)
                                              let Rdn := (BitVec.slice __opcode 0 3)
                                              (decode_aarch32_instrs_AND_r_T1enc_A_txt Rm Rdn))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                       __opcode 15 11)) == (0b00010#5 : (BitVec 5))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 2849) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2849
                                                  let imm5 := (BitVec.slice __opcode 6 5)
                                                  let Rm := (BitVec.slice __opcode 3 3)
                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                  (decode_aarch32_instrs_ASR_i_T1enc_A_txt imm5 Rm
                                                    Rd))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                           __opcode 15 6)) == (0b0100000100#10 : (BitVec 10))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 2850) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2850
                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                      let Rdn := (BitVec.slice __opcode 0 3)
                                                      (decode_aarch32_instrs_ASR_r_T1enc_A_txt Rm
                                                        Rdn))
                                                  else
                                                    (do
                                                      let w__28 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 15 12)) == (0xD#4 : (BitVec 4))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 8 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__26 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__26 <b 2852) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__28 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2852
                                                          let cond := (BitVec.slice __opcode 8 4)
                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                          (decode_aarch32_instrs_B_T1enc_A_txt cond
                                                            imm8))
                                                      else
                                                        (do
                                                          let w__30 ← (( do
                                                            if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                   __opcode 15 11)) == (0b11100#5 : (BitVec 5))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__29 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__29 <b 2853) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__30 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2853
                                                              let imm11 :=
                                                                (BitVec.slice __opcode 0 11)
                                                              (decode_aarch32_instrs_B_T2enc_A_txt
                                                                imm11))
                                                          else
                                                            (do
                                                              let w__32 ← (( do
                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                       __opcode 15 6)) == (0b0100001110#10 : (BitVec 10))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__31 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__31 <b 2863) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__32 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2863
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 3 3)
                                                                  let Rdn :=
                                                                    (BitVec.slice __opcode 0 3)
                                                                  (decode_aarch32_instrs_BIC_r_T1enc_A_txt
                                                                    Rm Rdn))
                                                              else
                                                                (do
                                                                  let w__34 ← (( do
                                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                           __opcode 15 8)) == (0xBE#8 : (BitVec 8))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__33 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__33 <b 2867) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__34 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2867
                                                                      let imm8 :=
                                                                        (BitVec.slice __opcode 0 8)
                                                                      (decode_aarch32_instrs_BKPT_T1enc_A_txt
                                                                        imm8))
                                                                  else
                                                                    (do
                                                                      let w__36 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 7)) == (0b010001111#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 2 0)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__35 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__35 <b 2873) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__36 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2873
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 3
                                                                              4)
                                                                          if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 2)])) != 0#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_BLX_r_T1enc_A_txt
                                                                                Rm)))
                                                                      else
                                                                        (do
                                                                          let w__38 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 7)) == (0b010001110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 2 0)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__37 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__37 <b 2875) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__38 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2875
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 4)
                                                                              if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 2)])) != 0#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_BX_T1enc_A_txt
                                                                                    Rm)))
                                                                          else
                                                                            (do
                                                                              let w__40 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         12)) == (0xB#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           10 10)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           8 8)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__39 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__39 <b 2878) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__40 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2878
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let i :=
                                                                                    (BitVec.slice
                                                                                      __opcode 9 1)
                                                                                  let imm5 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 3)
                                                                                  (decode_aarch32_instrs_CBNZ_T1enc_A_txt
                                                                                    op i imm5 Rn))
                                                                              else
                                                                                (do
                                                                                  let w__42 ← (( do
                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 6)) == (0b0100001011#10 : (BitVec 10))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__41 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__41 <b 2886) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__42 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2886
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          3)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          3)
                                                                                      (decode_aarch32_instrs_CMN_r_T1enc_A_txt
                                                                                        Rm Rn))
                                                                                  else
                                                                                    (do
                                                                                      let w__44 ← (( do
                                                                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 11)) == (0b00101#5 : (BitVec 5))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__43 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__43 <b 2890) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__44 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2890
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 3)
                                                                                          let imm8 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 8)
                                                                                          (decode_aarch32_instrs_CMP_i_T1enc_A_txt
                                                                                            Rn imm8))
                                                                                      else
                                                                                        (do
                                                                                          let w__46 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   6)) == (0b0100001010#10 : (BitVec 10))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__45 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__45 <b 2893) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__46 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2893
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  3
                                                                                                  3)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  3)
                                                                                              (decode_aarch32_instrs_CMP_r_T1enc_A_txt
                                                                                                Rm
                                                                                                Rn))
                                                                                          else
                                                                                            (do
                                                                                              let w__48 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       8)) == (0x45#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__47 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__47 <b 2894) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__48 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2894
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      1)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      3
                                                                                                      4)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      3)
                                                                                                  (decode_aarch32_instrs_CMP_r_T2enc_A_txt
                                                                                                    N
                                                                                                    Rm
                                                                                                    Rn))
                                                                                              else
                                                                                                (do
                                                                                                  let w__50 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           6)) == (0b0100000001#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__49 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__49 <b 2906) : Bool))))
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
                                                                                                      writeReg SEE 2906
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          3
                                                                                                          3)
                                                                                                      let Rdn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          3)
                                                                                                      (decode_aarch32_instrs_EOR_r_T1enc_A_txt
                                                                                                        Rm
                                                                                                        Rdn))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__52 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               8)) == (0xBF#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__51 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__51 <b 2911) : Bool))))
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
                                                                                                          writeReg SEE 2911
                                                                                                          let firstcond :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              4)
                                                                                                          let mask :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_IT_T1enc_A_txt
                                                                                                            firstcond
                                                                                                            mask))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__54 ← (( do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   11)) == (0b11001#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__53 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__53 <b 2917) : Bool))))
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
                                                                                                              writeReg SEE 2917
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  3)
                                                                                                              let register_list :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  8)
                                                                                                              (decode_aarch32_instrs_LDM_T1enc_A_txt
                                                                                                                Rn
                                                                                                                register_list))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__56 ← (( do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       11)) == (0b01111#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__55 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__55 <b 2924) : Bool))))
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
                                                                                                                  writeReg SEE 2924
                                                                                                                  let imm5 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      6
                                                                                                                      5)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      3)
                                                                                                                  let Rt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_aarch32_instrs_LDRB_i_T1enc_A_txt
                                                                                                                    imm5
                                                                                                                    Rn
                                                                                                                    Rt))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__58 ← (( do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           9)) == (0b0101110#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__57 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__57 <b 2930) : Bool))))
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
                                                                                                                      writeReg SEE 2930
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          6
                                                                                                                          3)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          3
                                                                                                                          3)
                                                                                                                      let Rt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_aarch32_instrs_LDRB_r_T1enc_A_txt
                                                                                                                        Rm
                                                                                                                        Rn
                                                                                                                        Rt))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__60 ← (( do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               11)) == (0b10001#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__59 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__59 <b 2949) : Bool))))
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
                                                                                                                          writeReg SEE 2949
                                                                                                                          let imm5 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              5)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              3
                                                                                                                              3)
                                                                                                                          let Rt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              3)
                                                                                                                          (decode_aarch32_instrs_LDRH_i_T1enc_A_txt
                                                                                                                            imm5
                                                                                                                            Rn
                                                                                                                            Rt))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__62 ← (( do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   9)) == (0b0101101#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__61 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__61 <b 2955) : Bool))))
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
                                                                                                                              writeReg SEE 2955
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  3)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  3
                                                                                                                                  3)
                                                                                                                              let Rt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  3)
                                                                                                                              (decode_aarch32_instrs_LDRH_r_T1enc_A_txt
                                                                                                                                Rm
                                                                                                                                Rn
                                                                                                                                Rt))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__64 ← (( do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       11)) == (0b01101#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__63 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__63 <b 2961) : Bool))))
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
                                                                                                                                  writeReg SEE 2961
                                                                                                                                  let imm5 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      5)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      3
                                                                                                                                      3)
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      3)
                                                                                                                                  (decode_aarch32_instrs_LDR_i_T1enc_A_txt
                                                                                                                                    imm5
                                                                                                                                    Rn
                                                                                                                                    Rt))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__66 ← (( do
                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           11)) == (0b10011#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__65 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__65 <b 2962) : Bool))))
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
                                                                                                                                      writeReg SEE 2962
                                                                                                                                      let Rt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          8
                                                                                                                                          3)
                                                                                                                                      let imm8 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          8)
                                                                                                                                      (decode_aarch32_instrs_LDR_i_T2enc_A_txt
                                                                                                                                        Rt
                                                                                                                                        imm8))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__68 ← (( do
                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               11)) == (0b01001#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__67 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__67 <b 2966) : Bool))))
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
                                                                                                                                          writeReg SEE 2966
                                                                                                                                          let Rt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              3)
                                                                                                                                          let imm8 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              8)
                                                                                                                                          (decode_aarch32_instrs_LDR_l_T1enc_A_txt
                                                                                                                                            Rt
                                                                                                                                            imm8))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__70 ← (( do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   9)) == (0b0101100#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__69 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__69 <b 2969) : Bool))))
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
                                                                                                                                              writeReg SEE 2969
                                                                                                                                              let Rm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  6
                                                                                                                                                  3)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  3
                                                                                                                                                  3)
                                                                                                                                              let Rt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  3)
                                                                                                                                              (decode_aarch32_instrs_LDR_r_T1enc_A_txt
                                                                                                                                                Rm
                                                                                                                                                Rn
                                                                                                                                                Rt))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__72 ← (( do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       9)) == (0b0101011#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__71 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__71 <b 2977) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__72 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2977
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      6
                                                                                                                                                      3)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      3
                                                                                                                                                      3)
                                                                                                                                                  let Rt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      3)
                                                                                                                                                  (decode_aarch32_instrs_LDRSB_r_T1enc_A_txt
                                                                                                                                                    Rm
                                                                                                                                                    Rn
                                                                                                                                                    Rt))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__74 ← (( do
                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           9)) == (0b0101111#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__73 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__73 <b 2988) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__74 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2988
                                                                                                                                                      let Rm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          6
                                                                                                                                                          3)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          3
                                                                                                                                                          3)
                                                                                                                                                      let Rt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          3)
                                                                                                                                                      (decode_aarch32_instrs_LDRSH_r_T1enc_A_txt
                                                                                                                                                        Rm
                                                                                                                                                        Rn
                                                                                                                                                        Rt))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__76 ← (( do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               11)) == (0b00000#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__75 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__75 <b 2996) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__76 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2996
                                                                                                                                                          let imm5 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              6
                                                                                                                                                              5)
                                                                                                                                                          let Rm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              3
                                                                                                                                                              3)
                                                                                                                                                          let Rd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              3)
                                                                                                                                                          (decode_aarch32_instrs_LSL_i_T1enc_A_txt
                                                                                                                                                            imm5
                                                                                                                                                            Rm
                                                                                                                                                            Rd))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__78 ← (( do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   6)) == (0b0100000010#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__77 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__77 <b 2997) : Bool))))
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
                                                                                                                                                              writeReg SEE 2997
                                                                                                                                                              let Rm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  3
                                                                                                                                                                  3)
                                                                                                                                                              let Rdn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  3)
                                                                                                                                                              (decode_aarch32_instrs_LSL_r_T1enc_A_txt
                                                                                                                                                                Rm
                                                                                                                                                                Rdn))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__80 ← (( do
                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       15
                                                                                                                                                                       11)) == (0b00001#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__79 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__79 <b 2999) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__80 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 2999
                                                                                                                                                                  let imm5 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      6
                                                                                                                                                                      5)
                                                                                                                                                                  let Rm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      3
                                                                                                                                                                      3)
                                                                                                                                                                  let Rd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      3)
                                                                                                                                                                  (decode_aarch32_instrs_LSR_i_T1enc_A_txt
                                                                                                                                                                    imm5
                                                                                                                                                                    Rm
                                                                                                                                                                    Rd))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__82 ← (( do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           6)) == (0b0100000011#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__81 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__81 <b 3000) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__82 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3000
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          3
                                                                                                                                                                          3)
                                                                                                                                                                      let Rdn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          3)
                                                                                                                                                                      (decode_aarch32_instrs_LSR_r_T1enc_A_txt
                                                                                                                                                                        Rm
                                                                                                                                                                        Rdn))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__84 ← (( do
                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               15
                                                                                                                                                                               11)) == (0b00100#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__83 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__83 <b 3011) : Bool))))
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
                                                                                                                                                                          writeReg SEE 3011
                                                                                                                                                                          let Rd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              8
                                                                                                                                                                              3)
                                                                                                                                                                          let imm8 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              8)
                                                                                                                                                                          (decode_aarch32_instrs_MOV_i_T1enc_A_txt
                                                                                                                                                                            Rd
                                                                                                                                                                            imm8))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__86 ← (( do
                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   15
                                                                                                                                                                                   8)) == (0x46#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__85 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__85 <b 3015) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__86 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3015
                                                                                                                                                                              let D :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  7
                                                                                                                                                                                  1)
                                                                                                                                                                              let Rm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  3
                                                                                                                                                                                  4)
                                                                                                                                                                              let Rd :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  3)
                                                                                                                                                                              (decode_aarch32_instrs_MOV_r_T1enc_A_txt
                                                                                                                                                                                D
                                                                                                                                                                                Rm
                                                                                                                                                                                Rd))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__88 ← (( do
                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       15
                                                                                                                                                                                       6)) == (0b0000000000#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__87 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__87 <b 3016) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__88 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3016
                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      3
                                                                                                                                                                                      3)
                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      3)
                                                                                                                                                                                  (decode_aarch32_instrs_MOV_r_T2enc_A_txt
                                                                                                                                                                                    Rm
                                                                                                                                                                                    Rd))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__90 ← (( do
                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           15
                                                                                                                                                                                           10)) == (0b010000#6 : (BitVec 6))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__89 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__89 <b 3019) : Bool))))
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
                                                                                                                                                                                      writeReg SEE 3019
                                                                                                                                                                                      let op :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          6
                                                                                                                                                                                          4)
                                                                                                                                                                                      let Rs :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          3
                                                                                                                                                                                          3)
                                                                                                                                                                                      let Rdm :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          3)
                                                                                                                                                                                      (decode_aarch32_instrs_MOV_rr_T1enc_A_txt
                                                                                                                                                                                        op
                                                                                                                                                                                        Rs
                                                                                                                                                                                        Rdm))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__92 ← (( do
                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               15
                                                                                                                                                                                               6)) == (0b0100001101#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__91 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__91 <b 3028) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__92 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 3028
                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              3
                                                                                                                                                                                              3)
                                                                                                                                                                                          let Rdm :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              0
                                                                                                                                                                                              3)
                                                                                                                                                                                          (decode_aarch32_instrs_MUL_T1enc_A_txt
                                                                                                                                                                                            Rn
                                                                                                                                                                                            Rdm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__94 ← (( do
                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   15
                                                                                                                                                                                                   6)) == (0b0100001111#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__93 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__93 <b 3033) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__94 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 3033
                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  3
                                                                                                                                                                                                  3)
                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  0
                                                                                                                                                                                                  3)
                                                                                                                                                                                              (decode_aarch32_instrs_MVN_r_T1enc_A_txt
                                                                                                                                                                                                Rm
                                                                                                                                                                                                Rd))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__96 ← (( do
                                                                                                                                                                                                if (((__opcode == 0b1011111100000000#16) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__95 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__95 <b 3037) : Bool))))
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
                                                                                                                                                                                                  writeReg SEE 3037
                                                                                                                                                                                                  (decode_aarch32_instrs_NOP_T1enc_A_txt
                                                                                                                                                                                                    ()))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let w__98 ← (( do
                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                           15
                                                                                                                                                                                                           6)) == (0b0100001100#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        let w__97 ← (( do
                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                          )
                                                                                                                                                                                                          :
                                                                                                                                                                                                          SailM
                                                                                                                                                                                                          Int
                                                                                                                                                                                                          )
                                                                                                                                                                                                        (pure (((w__97 <b 3044) : Bool))))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    :
                                                                                                                                                                                                    SailM
                                                                                                                                                                                                    Bool
                                                                                                                                                                                                    )
                                                                                                                                                                                                  if (w__98 : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 3044
                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          3
                                                                                                                                                                                                          3)
                                                                                                                                                                                                      let Rdn :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          0
                                                                                                                                                                                                          3)
                                                                                                                                                                                                      (decode_aarch32_instrs_ORR_r_T1enc_A_txt
                                                                                                                                                                                                        Rm
                                                                                                                                                                                                        Rdn))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let w__100 ← (( do
                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               15
                                                                                                                                                                                                               9)) == (0b1011110#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__99 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__99 <b 3062) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                        )
                                                                                                                                                                                                        :
                                                                                                                                                                                                        SailM
                                                                                                                                                                                                        Bool
                                                                                                                                                                                                        )
                                                                                                                                                                                                      if (w__100 : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 3062
                                                                                                                                                                                                          let P :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              8
                                                                                                                                                                                                              1)
                                                                                                                                                                                                          let register_list :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              0
                                                                                                                                                                                                              8)
                                                                                                                                                                                                          (decode_aarch32_instrs_POP_T1enc_A_txt
                                                                                                                                                                                                            P
                                                                                                                                                                                                            register_list))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let w__102 ← (( do
                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                   15
                                                                                                                                                                                                                   9)) == (0b1011010#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let w__101 ← (( do
                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                  :
                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                (pure (((w__101 <b 3063) : Bool))))
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
                                                                                                                                                                                                              writeReg SEE 3063
                                                                                                                                                                                                              let M :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  8
                                                                                                                                                                                                                  1)
                                                                                                                                                                                                              let register_list :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  0
                                                                                                                                                                                                                  8)
                                                                                                                                                                                                              (decode_aarch32_instrs_PUSH_T1enc_A_txt
                                                                                                                                                                                                                M
                                                                                                                                                                                                                register_list))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              let w__104 ← (( do
                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       15
                                                                                                                                                                                                                       6)) == (0b1011101001#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    let w__103 ← (( do
                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                      :
                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                    (pure (((w__103 <b 3087) : Bool))))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                )
                                                                                                                                                                                                                :
                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                )
                                                                                                                                                                                                              if (w__104 : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 3087
                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      3
                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      0
                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                  (decode_aarch32_instrs_REV16_T1enc_A_txt
                                                                                                                                                                                                                    Rm
                                                                                                                                                                                                                    Rd))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  let w__106 ← (( do
                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           15
                                                                                                                                                                                                                           6)) == (0b1011101000#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        let w__105 ← (( do
                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                          :
                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                        (pure (((w__105 <b 3090) : Bool))))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                    :
                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                  if (w__106 : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 3090
                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          3
                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          0
                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                      (decode_aarch32_instrs_REV_T1enc_A_txt
                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                        Rd))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      let w__108 ← (( do
                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               15
                                                                                                                                                                                                                               6)) == (0b1011101011#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            let w__107 ← (( do
                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                              :
                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                            (pure (((w__107 <b 3093) : Bool))))
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
                                                                                                                                                                                                                          writeReg SEE 3093
                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              3
                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              0
                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                          (decode_aarch32_instrs_REVSH_T1enc_A_txt
                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                            Rd))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          let w__110 ← (( do
                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                   15
                                                                                                                                                                                                                                   6)) == (0b0100000111#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let w__109 ← (( do
                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                (pure (((w__109 <b 3095) : Bool))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                            :
                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                          if (w__110 : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 3095
                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  3
                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                              let Rdn :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                              (decode_aarch32_instrs_ROR_r_T1enc_A_txt
                                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                                Rdn))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              let w__112 ← (( do
                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                       15
                                                                                                                                                                                                                                       6)) == (0b0100001001#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    let w__111 ← (( do
                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                    (pure (((w__111 <b 3097) : Bool))))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                              if (w__112 : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 3097
                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      3
                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                  (decode_aarch32_instrs_RSB_i_T1enc_A_txt
                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                    Rd))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  let w__114 ← (( do
                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                           6)) == (0b0100000110#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        let w__113 ← (( do
                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                        (pure (((w__113 <b 3116) : Bool))))
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
                                                                                                                                                                                                                                      writeReg SEE 3116
                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          3
                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                      let Rdn :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                      (decode_aarch32_instrs_SBC_r_T1enc_A_txt
                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                        Rdn))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      let w__116 ← (( do
                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 15
                                                                                                                                                                                                                                                 4)) == (0xB65#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 2
                                                                                                                                                                                                                                                 0)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            let w__115 ← (( do
                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                            (pure (((w__115 <b 3126) : Bool))))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                      if (w__116 : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 3126
                                                                                                                                                                                                                                          let E :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              3
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     2)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (decode_aarch32_instrs_SETEND_T1enc_A_txt
                                                                                                                                                                                                                                                E)))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          let w__118 ← (( do
                                                                                                                                                                                                                                            if (((__opcode == 0b1011111101000000#16) : Bool) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                let w__117 ← (( do
                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                (pure (((w__117 <b 3128) : Bool))))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                          if (w__118 : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 3128
                                                                                                                                                                                                                                              (decode_aarch32_instrs_SEV_T1enc_A_txt
                                                                                                                                                                                                                                                ()))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              let w__120 ← (( do
                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       15
                                                                                                                                                                                                                                                       11)) == (0b11000#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    let w__119 ← (( do
                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                    (pure (((w__119 <b 3187) : Bool))))
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
                                                                                                                                                                                                                                                  writeReg SEE 3187
                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      8
                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                  let register_list :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                      8)
                                                                                                                                                                                                                                                  (decode_aarch32_instrs_STM_T1enc_A_txt
                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                    register_list))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  let w__122 ← (( do
                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                                           11)) == (0b01110#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        let w__121 ← (( do
                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                        (pure (((w__121 <b 3194) : Bool))))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                  if (w__122 : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 3194
                                                                                                                                                                                                                                                      let imm5 :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          6
                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          3
                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                      (decode_aarch32_instrs_STRB_i_T1enc_A_txt
                                                                                                                                                                                                                                                        imm5
                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                        Rt))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      let w__124 ← (( do
                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                               15
                                                                                                                                                                                                                                                               9)) == (0b0101010#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            let w__123 ← (( do
                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                            (pure (((w__123 <b 3198) : Bool))))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                      if (w__124 : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 3198
                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              6
                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              3
                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                          let Rt :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                          (decode_aarch32_instrs_STRB_r_T1enc_A_txt
                                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                            Rt))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          let w__126 ← (( do
                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                   15
                                                                                                                                                                                                                                                                   11)) == (0b10000#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                let w__125 ← (( do
                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                (pure (((w__125 <b 3215) : Bool))))
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
                                                                                                                                                                                                                                                              writeReg SEE 3215
                                                                                                                                                                                                                                                              let imm5 :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  6
                                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  3
                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                              let Rt :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                              (decode_aarch32_instrs_STRH_i_T1enc_A_txt
                                                                                                                                                                                                                                                                imm5
                                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                                Rt))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              let w__128 ← (( do
                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       15
                                                                                                                                                                                                                                                                       9)) == (0b0101001#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    let w__127 ← (( do
                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                    (pure (((w__127 <b 3219) : Bool))))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                              if (w__128 : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 3219
                                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      6
                                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      3
                                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_STRH_r_T1enc_A_txt
                                                                                                                                                                                                                                                                    Rm
                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                    Rt))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  let w__130 ← (( do
                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                                                           11)) == (0b01100#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let w__129 ← (( do
                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                        (pure (((w__129 <b 3225) : Bool))))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                  if (w__130 : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 3225
                                                                                                                                                                                                                                                                      let imm5 :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          6
                                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          3
                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_STR_i_T1enc_A_txt
                                                                                                                                                                                                                                                                        imm5
                                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                                        Rt))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      let w__132 ← (( do
                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                               15
                                                                                                                                                                                                                                                                               11)) == (0b10010#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            let w__131 ← (( do
                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                            (pure (((w__131 <b 3226) : Bool))))
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
                                                                                                                                                                                                                                                                          writeReg SEE 3226
                                                                                                                                                                                                                                                                          let Rt :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              8
                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                          let imm8 :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                              8)
                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_STR_i_T2enc_A_txt
                                                                                                                                                                                                                                                                            Rt
                                                                                                                                                                                                                                                                            imm8))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          let w__134 ← (( do
                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                   15
                                                                                                                                                                                                                                                                                   9)) == (0b0101000#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                let w__133 ← (( do
                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                (pure (((w__133 <b 3230) : Bool))))
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
                                                                                                                                                                                                                                                                              writeReg SEE 3230
                                                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  6
                                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  3
                                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                                              let Rt :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_STR_r_T1enc_A_txt
                                                                                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                                                Rt))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              let w__136 ← (( do
                                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                       15
                                                                                                                                                                                                                                                                                       9)) == (0b0001111#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                    let w__135 ← (( do
                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                    (pure (((w__135 <b 3236) : Bool))))
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
                                                                                                                                                                                                                                                                                  writeReg SEE 3236
                                                                                                                                                                                                                                                                                  let imm3 :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      6
                                                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      3
                                                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                      3)
                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_SUB_i_T1enc_A_txt
                                                                                                                                                                                                                                                                                    imm3
                                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                                    Rd))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  let w__138 ← (( do
                                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                                                                           11)) == (0b00111#5 : (BitVec 5))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                        let w__137 ← (( do
                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                        (pure (((w__137 <b 3237) : Bool))))
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
                                                                                                                                                                                                                                                                                      writeReg SEE 3237
                                                                                                                                                                                                                                                                                      let Rdn :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          8
                                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                                      let imm8 :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                          8)
                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_SUB_i_T2enc_A_txt
                                                                                                                                                                                                                                                                                        Rdn
                                                                                                                                                                                                                                                                                        imm8))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      let w__140 ← (( do
                                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               15
                                                                                                                                                                                                                                                                                               9)) == (0b0001101#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                            let w__139 ← (( do
                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                            (pure (((w__139 <b 3242) : Bool))))
                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                      if (w__140 : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          writeReg SEE 3242
                                                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              6
                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              3
                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_SUB_r_T1enc_A_txt
                                                                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                                                            Rd))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          let w__142 ← (( do
                                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                   15
                                                                                                                                                                                                                                                                                                   7)) == (0b101100001#9 : (BitVec 9))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                let w__141 ← (( do
                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                (pure (((w__141 <b 3246) : Bool))))
                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                          if (w__142 : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              writeReg SEE 3246
                                                                                                                                                                                                                                                                                              let imm7 :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                                  7)
                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_SUB_SP_i_T1enc_A_txt
                                                                                                                                                                                                                                                                                                imm7))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              let w__144 ← (( do
                                                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                                       15
                                                                                                                                                                                                                                                                                                       8)) == (0xDF#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                    let w__143 ← (( do
                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                    (pure (((w__143 <b 3252) : Bool))))
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
                                                                                                                                                                                                                                                                                                  writeReg SEE 3252
                                                                                                                                                                                                                                                                                                  let imm8 :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                                      8)
                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_SVC_T1enc_A_txt
                                                                                                                                                                                                                                                                                                    imm8))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  let w__146 ← (( do
                                                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                                                                                           6)) == (0b1011001001#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                        let w__145 ← (( do
                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                        (pure (((w__145 <b 3262) : Bool))))
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
                                                                                                                                                                                                                                                                                                      writeReg SEE 3262
                                                                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          3
                                                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_SXTB_T1enc_A_txt
                                                                                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                                                                                        Rd))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      let w__148 ← (( do
                                                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                                               15
                                                                                                                                                                                                                                                                                                               6)) == (0b1011001000#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                                            let w__147 ← (( do
                                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                            (pure (((w__147 <b 3265) : Bool))))
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
                                                                                                                                                                                                                                                                                                          writeReg SEE 3265
                                                                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                              3
                                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_SXTH_T1enc_A_txt
                                                                                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                                                                                            Rd))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          let w__150 ← (( do
                                                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                                   15
                                                                                                                                                                                                                                                                                                                   6)) == (0b0100001000#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                                let w__149 ← (( do
                                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                (pure (((w__149 <b 3276) : Bool))))
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
                                                                                                                                                                                                                                                                                                              writeReg SEE 3276
                                                                                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                  3
                                                                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                                                  3)
                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_TST_r_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                                                                                                                Rn))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              let w__152 ← (( do
                                                                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                                                       15
                                                                                                                                                                                                                                                                                                                       8)) == (0xDE#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                                    let w__151 ← (( do
                                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                    (pure (((w__151 <b 3288) : Bool))))
                                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                              if (w__152 : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  writeReg SEE 3288
                                                                                                                                                                                                                                                                                                                  let imm8 :=
                                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                                                      8)
                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_UDF_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                    imm8))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  let w__154 ← (( do
                                                                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                                                                                                           6)) == (0b1011001011#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                                        let w__153 ← (( do
                                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                        (pure (((w__153 <b 3345) : Bool))))
                                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                  if (w__154 : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      writeReg SEE 3345
                                                                                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                                          3
                                                                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                                                          3)
                                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_UXTB_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                                                                                                        Rd))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      let w__156 ← (( do
                                                                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                                                               15
                                                                                                                                                                                                                                                                                                                               6)) == (0b1011001010#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                                                            let w__155 ← (( do
                                                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                            (pure (((w__155 <b 3348) : Bool))))
                                                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                      if (w__156 : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          writeReg SEE 3348
                                                                                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                                              3
                                                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_UXTH_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                                                                                                            Rd))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          let w__158 ← (( do
                                                                                                                                                                                                                                                                                                                            if (((__opcode == 0b1011111100100000#16) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                                                let w__157 ← (( do
                                                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                (pure (((w__157 <b 3761) : Bool))))
                                                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                          if (w__158 : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              writeReg SEE 3761
                                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_WFE_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                                ()))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              let w__160 ← (( do
                                                                                                                                                                                                                                                                                                                                if (((__opcode == 0b1011111100110000#16) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                                                    let w__159 ← (( do
                                                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                    (pure (((w__159 <b 3764) : Bool))))
                                                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                              if (w__160 : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  writeReg SEE 3764
                                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_WFI_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                                    ()))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  let w__162 ← (( do
                                                                                                                                                                                                                                                                                                                                    if (((__opcode == 0b1011111100010000#16) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                                                        let w__161 ← (( do
                                                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                        (pure (((w__161 <b 3767) : Bool))))
                                                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                  if (w__162 : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      writeReg SEE 3767
                                                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_YIELD_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                                        ()))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      let w__164 ← (( do
                                                                                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                                                 15
                                                                                                                                                                                                                                                                                                                                                 5)) == (0b10110110011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                                                 3
                                                                                                                                                                                                                                                                                                                                                 3)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                                                                            let w__163 ← (( do
                                                                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                            (pure (((w__163 <b 3770) : Bool))))
                                                                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                      if (w__164 : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          writeReg SEE 3770
                                                                                                                                                                                                                                                                                                                                          let im :=
                                                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                                                              4
                                                                                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                                                                                          let A :=
                                                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                                                              2
                                                                                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                                                                                          let I :=
                                                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                                                              1
                                                                                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                                                                                          let F :=
                                                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_CPS_T1enc_AS_txt
                                                                                                                                                                                                                                                                                                                                            im
                                                                                                                                                                                                                                                                                                                                            A
                                                                                                                                                                                                                                                                                                                                            I
                                                                                                                                                                                                                                                                                                                                            F))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          let w__166 ← (( do
                                                                                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                                                                   15
                                                                                                                                                                                                                                                                                                                                                   6)) == (0b1011101010#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                                                                let w__165 ← (( do
                                                                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                (pure (((w__165 <b 3814) : Bool))))
                                                                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                          if (w__166 : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              writeReg SEE 3814
                                                                                                                                                                                                                                                                                                                                              let imm6 :=
                                                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                                                                                  6)
                                                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_HLT_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                                                imm6))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              let w__168 ← (( do
                                                                                                                                                                                                                                                                                                                                                if (((__opcode == 0b1011111101010000#16) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                                                                    let w__167 ← (( do
                                                                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                    (pure (((w__167 <b 3830) : Bool))))
                                                                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                              if (w__168 : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  writeReg SEE 3830
                                                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_SEVL_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                                                    ()))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  let w__170 ← (( do
                                                                                                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                                                                             15
                                                                                                                                                                                                                                                                                                                                                             4)) == (0xB61#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                                                                             2
                                                                                                                                                                                                                                                                                                                                                             0)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                                                                        let w__169 ← (( do
                                                                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                        (pure (((w__169 <b 3889) : Bool))))
                                                                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                  if (w__170 : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      writeReg SEE 3889
                                                                                                                                                                                                                                                                                                                                                      let imm1 :=
                                                                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                                                                          3
                                                                                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                                                                                     4)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                                                                                     0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                                                                                   1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                                                                 2)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_SETPAN_T1enc_A_txt
                                                                                                                                                                                                                                                                                                                                                            imm1)))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    sailThrow ((Error_Undefined
                                                                                                                                                                                                                                                                                                                                                      ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
