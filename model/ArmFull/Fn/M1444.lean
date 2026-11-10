import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0233
import ArmFull.Fn.M0234
import ArmFull.Fn.M0235
import ArmFull.Fn.M0839
import ArmFull.Fn.M1285

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
def __DecodeT32__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__340 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xF84#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
             __opcode 11 8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
    then
      (do
        let w__339 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__339 <b 3234) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__340 : Bool)
  then
    (do
      writeReg SEE 3234
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      let imm8 := (BitVec.slice __opcode 0 8)
      (decode_aarch32_instrs_STRT_T1enc_A_txt Rn Rt imm8)
      (pure false))
  else
    (do
      let w__342 ← (( do
        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 25 21)) == (0b01101#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
        then
          (do
            let w__341 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__341 <b 3238) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__342 : Bool)
      then
        (do
          writeReg SEE 3238
          let i := (BitVec.slice __opcode 26 1)
          let S := (BitVec.slice __opcode 20 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let imm3 := (BitVec.slice __opcode 12 3)
          let Rd := (BitVec.slice __opcode 8 4)
          let imm8 := (BitVec.slice __opcode 0 8)
          (decode_aarch32_instrs_SUB_i_T3enc_A_txt i S Rn imm3 Rd imm8)
          (pure false))
      else
        (do
          let w__344 ← (( do
            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 25 20)) == (0b101010#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__343 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__343 <b 3239) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__344 : Bool)
          then
            (do
              writeReg SEE 3239
              let i := (BitVec.slice __opcode 26 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let imm3 := (BitVec.slice __opcode 12 3)
              let Rd := (BitVec.slice __opcode 8 4)
              let imm8 := (BitVec.slice __opcode 0 8)
              (decode_aarch32_instrs_SUB_i_T4enc_A_txt i Rn imm3 Rd imm8)
              (pure false))
          else
            (do
              let w__346 ← (( do
                if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb __opcode 31 8)) == (0xF3DE8F#24 : (BitVec 24))) : Bool) : Bool)
                then
                  (do
                    let w__345 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__345 <b 3240) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__346 : Bool)
              then
                (do
                  writeReg SEE 3240
                  let Rn := (BitVec.slice __opcode 16 4)
                  let imm8 := (BitVec.slice __opcode 0 8)
                  if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 19)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 11)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_SUB_i_T5enc_A_txt Rn imm8))
                  (pure false))
              else
                (do
                  let w__348 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11101011101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                    then
                      (do
                        let w__347 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__347 <b 3243) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__348 : Bool)
                  then
                    (do
                      writeReg SEE 3243
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
                          (decode_aarch32_instrs_SUB_r_T2enc_A_txt S Rn imm3 Rd imm2 stype Rm))
                      (pure false))
                  else
                    (do
                      let w__350 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31
                                 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                   __opcode 25 21)) == (0b01101#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                   __opcode 19 15)) == (0b11010#5 : (BitVec 5))))) : Bool) : Bool)
                        then
                          (do
                            let w__349 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__349 <b 3247) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__350 : Bool)
                      then
                        (do
                          writeReg SEE 3247
                          let i := (BitVec.slice __opcode 26 1)
                          let S := (BitVec.slice __opcode 20 1)
                          let imm3 := (BitVec.slice __opcode 12 3)
                          let Rd := (BitVec.slice __opcode 8 4)
                          let imm8 := (BitVec.slice __opcode 0 8)
                          (decode_aarch32_instrs_SUB_SP_i_T2enc_A_txt i S imm3 Rd imm8)
                          (pure false))
                      else
                        (do
                          let w__352 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode
                                     31 27)) == (0b11110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                     __opcode 25 15)) == (0b10101011010#11 : (BitVec 11)))) : Bool) : Bool)
                            then
                              (do
                                let w__351 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__351 <b 3248) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__352 : Bool)
                          then
                            (do
                              writeReg SEE 3248
                              let i := (BitVec.slice __opcode 26 1)
                              let imm3 := (BitVec.slice __opcode 12 3)
                              let Rd := (BitVec.slice __opcode 8 4)
                              let imm8 := (BitVec.slice __opcode 0 8)
                              (decode_aarch32_instrs_SUB_SP_i_T3enc_A_txt i imm3 Rd imm8)
                              (pure false))
                          else
                            (do
                              let w__354 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11101011101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                         __opcode 19 15)) == (0b11010#5 : (BitVec 5)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__353 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__353 <b 3250) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__354 : Bool)
                              then
                                (do
                                  writeReg SEE 3250
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
                                      (decode_aarch32_instrs_SUB_SP_r_T1enc_A_txt S imm3 Rd imm2
                                        stype Rm))
                                  (pure false))
                              else
                                (do
                                  let w__356 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xFA2#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 7 6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__355 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__355 <b 3254) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__356 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3254
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rd := (BitVec.slice __opcode 8 4)
                                      let rotate := (BitVec.slice __opcode 4 2)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode
                                               6)])) != 0#1) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_SXTAB16_T1enc_A_txt Rn Rd rotate Rm))
                                      (pure false))
                                  else
                                    (do
                                      let w__358 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xFA4#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 7 6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__357 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__357 <b 3256) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__358 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3256
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rd := (BitVec.slice __opcode 8 4)
                                          let rotate := (BitVec.slice __opcode 4 2)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 6)])) != 0#1) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_SXTAB_T1enc_A_txt Rn Rd rotate
                                                Rm))
                                          (pure false))
                                      else
                                        (do
                                          let w__360 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xFA0#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 7 6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__359 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__359 <b 3258) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__360 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3258
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Rd := (BitVec.slice __opcode 8 4)
                                              let rotate := (BitVec.slice __opcode 4 2)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 6)])) != 0#1) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_SXTAH_T1enc_A_txt Rn Rd
                                                    rotate Rm))
                                              (pure false))
                                          else
                                            (do
                                              let w__362 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                         __opcode 31 12)) == (0xFA2FF#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__361 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__361 <b 3260) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__362 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3260
                                                  let Rd := (BitVec.slice __opcode 8 4)
                                                  let rotate := (BitVec.slice __opcode 4 2)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 6)])) != 0#1) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_SXTB16_T1enc_A_txt Rd
                                                        rotate Rm))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__364 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                             __opcode 31 12)) == (0xFA4FF#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__363 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__363 <b 3263) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__364 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3263
                                                      let Rd := (BitVec.slice __opcode 8 4)
                                                      let rotate := (BitVec.slice __opcode 4 2)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 6)])) != 0#1) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_SXTB_T2enc_A_txt Rd
                                                            rotate Rm))
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__366 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                 __opcode 31 12)) == (0xFA0FF#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                 __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__365 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__365 <b 3266) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__366 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3266
                                                          let Rd := (BitVec.slice __opcode 8 4)
                                                          let rotate := (BitVec.slice __opcode 4 2)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 6)])) != 0#1) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_aarch32_instrs_SXTH_T2enc_A_txt
                                                                Rd rotate Rm))
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__368 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 15 5)) == (0b11110000000#11 : (BitVec 11)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__367 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__367 <b 3267) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__368 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3267
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let H := (BitVec.slice __opcode 4 1)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 11)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_TBB_T1enc_A_txt
                                                                    Rn H Rm))
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__370 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                         __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 25 20)) == (0b001001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 15 15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 11 8)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__369 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__369 <b 3269) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__370 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3269
                                                                  let i :=
                                                                    (BitVec.slice __opcode 26 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let imm3 :=
                                                                    (BitVec.slice __opcode 12 3)
                                                                  let imm8 :=
                                                                    (BitVec.slice __opcode 0 8)
                                                                  (decode_aarch32_instrs_TEQ_i_T1enc_A_txt
                                                                    i Rn imm3 imm8)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__372 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xEA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 11 8)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__371 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__371 <b 3271) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__372 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3271
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let imm3 :=
                                                                        (BitVec.slice __opcode 12 3)
                                                                      let imm2 :=
                                                                        (BitVec.slice __opcode 6 2)
                                                                      let stype :=
                                                                        (BitVec.slice __opcode 4 2)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 15)])) != 0#1) : Bool)
                                                                      then
                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                          ()))
                                                                      else
                                                                        (do
                                                                          (decode_aarch32_instrs_TEQ_r_T1enc_A_txt
                                                                            Rn imm3 imm2 stype Rm))
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__374 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 25 20)) == (0b000001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__373 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__373 <b 3274) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__374 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3274
                                                                          let i :=
                                                                            (BitVec.slice __opcode
                                                                              26 1)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let imm3 :=
                                                                            (BitVec.slice __opcode
                                                                              12 3)
                                                                          let imm8 :=
                                                                            (BitVec.slice __opcode 0
                                                                              8)
                                                                          (decode_aarch32_instrs_TST_i_T1enc_A_txt
                                                                            i Rn imm3 imm8)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__376 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xEA1#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 11 8)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__375 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__375 <b 3277) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__376 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3277
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let imm3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 3)
                                                                              let imm2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 2)
                                                                              let stype :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 2)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 15)])) != 0#1) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_TST_r_T2enc_A_txt
                                                                                    Rn imm3 imm2
                                                                                    stype Rm))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__378 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           7 4)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__377 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__377 <b 3280) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__378 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3280
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_UADD16_T1enc_A_txt
                                                                                    Rn Rd Rm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__380 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               7 4)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__379 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__379 <b 3282) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__380 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3282
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_UADD8_T1enc_A_txt
                                                                                        Rn Rd Rm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__382 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   7
                                                                                                   4)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__381 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__381 <b 3284) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__382 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3284
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_UASX_T1enc_A_txt
                                                                                            Rn Rd Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__384 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xF3C#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       5
                                                                                                       5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__383 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__383 <b 3286) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__384 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3286
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
                                                                                              let widthm1 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         5)])) != 0#1)) : Bool)
                                                                                              then
                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                  ()))
                                                                                              else
                                                                                                (do
                                                                                                  (decode_aarch32_instrs_UBFX_T1enc_A_txt
                                                                                                    Rn
                                                                                                    imm3
                                                                                                    Rd
                                                                                                    imm2
                                                                                                    widthm1))
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__386 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xF7F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         12)) == (0xA#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__385 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__385 <b 3289) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__386 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3289
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let imm12 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      12)
                                                                                                  (decode_aarch32_instrs_UDF_T2enc_A_txt
                                                                                                    imm4
                                                                                                    imm12)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__388 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xFBB#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             7
                                                                                                             4)) == (0xF#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__387 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__387 <b 3291) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__388 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3291
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Ra :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
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
                                                                                                      (decode_aarch32_instrs_UDIV_T1enc_A_txt
                                                                                                        Rn
                                                                                                        Ra
                                                                                                        Rd
                                                                                                        Rm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__390 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   7
                                                                                                                   4)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__389 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__389 <b 3293) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__390 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3293
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
                                                                                                          (decode_aarch32_instrs_UHADD16_T1enc_A_txt
                                                                                                            Rn
                                                                                                            Rd
                                                                                                            Rm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__392 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       7
                                                                                                                       4)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__391 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__391 <b 3295) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__392 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3295
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
                                                                                                              (decode_aarch32_instrs_UHADD8_T1enc_A_txt
                                                                                                                Rn
                                                                                                                Rd
                                                                                                                Rm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__394 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           7
                                                                                                                           4)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__393 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__393 <b 3297) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__394 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3297
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
                                                                                                                  (decode_aarch32_instrs_UHASX_T1enc_A_txt
                                                                                                                    Rn
                                                                                                                    Rd
                                                                                                                    Rm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__396 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xFAE#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               7
                                                                                                                               4)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__395 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__395 <b 3299) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__396 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3299
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
                                                                                                                      (decode_aarch32_instrs_UHSAX_T1enc_A_txt
                                                                                                                        Rn
                                                                                                                        Rd
                                                                                                                        Rm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__398 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xFAD#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   7
                                                                                                                                   4)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__397 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__397 <b 3301) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__398 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3301
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
                                                                                                                          (decode_aarch32_instrs_UHSUB16_T1enc_A_txt
                                                                                                                            Rn
                                                                                                                            Rd
                                                                                                                            Rm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__400 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xFAC#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       7
                                                                                                                                       4)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__399 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__399 <b 3303) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__400 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3303
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
                                                                                                                              (decode_aarch32_instrs_UHSUB8_T1enc_A_txt
                                                                                                                                Rn
                                                                                                                                Rd
                                                                                                                                Rm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__402 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xFBE#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         7
                                                                                                                                         4)) == (0x6#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__401 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__401 <b 3305) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__402 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3305
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let RdLo :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let RdHi :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      8
                                                                                                                                      4)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_aarch32_instrs_UMAAL_T1enc_A_txt
                                                                                                                                    Rn
                                                                                                                                    RdLo
                                                                                                                                    RdHi
                                                                                                                                    Rm)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__404 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xFBE#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             7
                                                                                                                                             4)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__403 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__403 <b 3307) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__404 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3307
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let RdLo :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          4)
                                                                                                                                      let RdHi :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          8
                                                                                                                                          4)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_aarch32_instrs_UMLAL_T1enc_A_txt
                                                                                                                                        Rn
                                                                                                                                        RdLo
                                                                                                                                        RdHi
                                                                                                                                        Rm)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__406 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xFBA#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 7
                                                                                                                                                 4)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__405 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__405 <b 3309) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__406 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3309
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let RdLo :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              4)
                                                                                                                                          let RdHi :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              4)
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              4)
                                                                                                                                          (decode_aarch32_instrs_UMULL_T1enc_A_txt
                                                                                                                                            Rn
                                                                                                                                            RdLo
                                                                                                                                            RdHi
                                                                                                                                            Rm)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__408 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       7
                                                                                                                                                       4)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__407 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__407 <b 3311) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__408 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3311
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
                                                                                                                                              (decode_aarch32_instrs_UQADD16_T1enc_A_txt
                                                                                                                                                Rn
                                                                                                                                                Rd
                                                                                                                                                Rm)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__410 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           7
                                                                                                                                                           4)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__409 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__409 <b 3313) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__410 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 3313
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
                                                                                                                                                  (decode_aarch32_instrs_UQADD8_T1enc_A_txt
                                                                                                                                                    Rn
                                                                                                                                                    Rd
                                                                                                                                                    Rm)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__412 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               7
                                                                                                                                                               4)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__411 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__411 <b 3315) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__412 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3315
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
                                                                                                                                                      (decode_aarch32_instrs_UQASX_T1enc_A_txt
                                                                                                                                                        Rn
                                                                                                                                                        Rd
                                                                                                                                                        Rm)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__414 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 20)) == (0xFAE#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   7
                                                                                                                                                                   4)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__413 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__413 <b 3317) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__414 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 3317
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
                                                                                                                                                          (decode_aarch32_instrs_UQSAX_T1enc_A_txt
                                                                                                                                                            Rn
                                                                                                                                                            Rd
                                                                                                                                                            Rm)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__416 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     20)) == (0xFAD#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       15
                                                                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       7
                                                                                                                                                                       4)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__415 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__415 <b 3319) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__416 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3319
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
                                                                                                                                                              (decode_aarch32_instrs_UQSUB16_T1enc_A_txt
                                                                                                                                                                Rn
                                                                                                                                                                Rd
                                                                                                                                                                Rm)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__418 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         20)) == (0xFAC#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           7
                                                                                                                                                                           4)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__417 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__417 <b 3321) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__418 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 3321
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
                                                                                                                                                                  (decode_aarch32_instrs_UQSUB8_T1enc_A_txt
                                                                                                                                                                    Rn
                                                                                                                                                                    Rd
                                                                                                                                                                    Rm)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__420 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             20)) == (0xFB7#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               15
                                                                                                                                                                               12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               7
                                                                                                                                                                               4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__419 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__419 <b 3323) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__420 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3323
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
                                                                                                                                                                      (decode_aarch32_instrs_USAD8_T1enc_A_txt
                                                                                                                                                                        Rn
                                                                                                                                                                        Rd
                                                                                                                                                                        Rm)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__422 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 20)) == (0xFB7#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 7
                                                                                                                                                                                 4)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__421 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__421 <b 3325) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__422 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3325
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              4)
                                                                                                                                                                          let Ra :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
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
                                                                                                                                                                          (decode_aarch32_instrs_USADA8_T1enc_A_txt
                                                                                                                                                                            Rn
                                                                                                                                                                            Ra
                                                                                                                                                                            Rd
                                                                                                                                                                            Rm)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__424 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     20)) == (0xF3A#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       15
                                                                                                                                                                                       12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       7
                                                                                                                                                                                       4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__423 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__423 <b 3327) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__424 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3327
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
                                                                                                                                                                              let sat_imm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  4)
                                                                                                                                                                              if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         5)])) != 0#1)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                  ()))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  (decode_aarch32_instrs_USAT16_T1enc_A_txt
                                                                                                                                                                                    Rn
                                                                                                                                                                                    Rd
                                                                                                                                                                                    sat_imm))
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
