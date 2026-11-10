import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0233
import ArmFull.Fn.M0234
import ArmFull.Fn.M0235
import ArmFull.Fn.M0236
import ArmFull.Fn.M0579
import ArmFull.Fn.M0839
import ArmFull.Fn.M0842
import ArmFull.Fn.M0853
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
def __DecodeA32_DataProMisc__seg3 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__272 ← (( do
    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                 __opcode 11 4)) == (0x0F#8 : (BitVec 8)))))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__270 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__270 <b 3205) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__272 : Bool)
  then
    (do
      writeReg SEE 3205
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      let Rm := (BitVec.slice __opcode 0 4)
      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 __opcode 11)])) != 0#1)) : Bool)
      then sailThrow ((Error_ConstrainedUnpredictable ()))
      else
        (do
          (decode_aarch32_instrs_STRD_r_A1enc_A_txt cond P U W Rn Rt Rm))
      (pure false))
  else
    (do
      let w__275 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x18#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                 __opcode 11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__273 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__273 <b 3206) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__275 : Bool)
      then
        (do
          writeReg SEE 3206
          let cond := (BitVec.slice __opcode 28 4)
          let Rn := (BitVec.slice __opcode 16 4)
          let Rd := (BitVec.slice __opcode 12 4)
          let Rt := (BitVec.slice __opcode 0 4)
          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 9)])) != 1#1)) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_aarch32_instrs_STREX_A1enc_A_txt cond Rn Rd Rt))
          (pure false))
      else
        (do
          let w__278 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x1C#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                     __opcode 11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__276 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__276 <b 3208) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__278 : Bool)
          then
            (do
              writeReg SEE 3208
              let cond := (BitVec.slice __opcode 28 4)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rd := (BitVec.slice __opcode 12 4)
              let Rt := (BitVec.slice __opcode 0 4)
              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 9)])) != 1#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_STREXB_A1enc_A_txt cond Rn Rd Rt))
              (pure false))
          else
            (do
              let w__281 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x1A#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                         __opcode 11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__279 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__279 <b 3210) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__281 : Bool)
              then
                (do
                  writeReg SEE 3210
                  let cond := (BitVec.slice __opcode 28 4)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rd := (BitVec.slice __opcode 12 4)
                  let Rt := (BitVec.slice __opcode 0 4)
                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 9)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_STREXD_A1enc_A_txt cond Rn Rd Rt))
                  (pure false))
              else
                (do
                  let w__284 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                             __opcode 11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__282 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__282 <b 3212) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__284 : Bool)
                  then
                    (do
                      writeReg SEE 3212
                      let cond := (BitVec.slice __opcode 28 4)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rd := (BitVec.slice __opcode 12 4)
                      let Rt := (BitVec.slice __opcode 0 4)
                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 9)])) != 1#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_STREXH_A1enc_A_txt cond Rn Rd Rt))
                      (pure false))
                  else
                    (do
                      let w__287 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27
                                 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 7 4)) == (0xB#4 : (BitVec 4)))))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__285 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__285 <b 3214) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__287 : Bool)
                      then
                        (do
                          writeReg SEE 3214
                          let cond := (BitVec.slice __opcode 28 4)
                          let P := (BitVec.slice __opcode 24 1)
                          let U := (BitVec.slice __opcode 23 1)
                          let W := (BitVec.slice __opcode 21 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let imm4H := (BitVec.slice __opcode 8 4)
                          let imm4L := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_STRH_i_A1enc_A_txt cond P U W Rn Rt imm4H imm4L)
                          (pure false))
                      else
                        (do
                          let w__290 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 11 4)) == (0x0B#8 : (BitVec 8)))))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__288 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__288 <b 3218) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__290 : Bool)
                          then
                            (do
                              writeReg SEE 3218
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let Rm := (BitVec.slice __opcode 0 4)
                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 11)])) != 0#1)) : Bool)
                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                              else
                                (do
                                  (decode_aarch32_instrs_STRH_r_A1enc_A_txt cond P U W Rn Rt Rm))
                              (pure false))
                          else
                            (do
                              let w__293 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 22 20)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 7 4)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__291 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__291 <b 3221) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__293 : Bool)
                              then
                                (do
                                  writeReg SEE 3221
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let imm4H := (BitVec.slice __opcode 8 4)
                                  let imm4L := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_STRHT_A1enc_A_txt cond U Rn Rt imm4H imm4L)
                                  (pure false))
                              else
                                (do
                                  let w__296 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 22 20)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                               __opcode 11 4)) == (0x0B#8 : (BitVec 8))))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__294 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__294 <b 3222) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__296 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3222
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let U := (BitVec.slice __opcode 23 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rt := (BitVec.slice __opcode 12 4)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 11)])) != 0#1)) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_STRHT_A2enc_A_txt cond U Rn Rt Rm))
                                      (pure false))
                                  else
                                    (do
                                      let w__299 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                               __opcode 27 21)) == (0b0010010#7 : (BitVec 7))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__297 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__297 <b 3235) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__299 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3235
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let S := (BitVec.slice __opcode 20 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rd := (BitVec.slice __opcode 12 4)
                                          let imm12 := (BitVec.slice __opcode 0 12)
                                          (decode_aarch32_instrs_SUB_i_A1enc_A_txt cond S Rn Rd
                                            imm12)
                                          (pure false))
                                      else
                                        (do
                                          let w__302 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                     __opcode 27 21)) == (0b0000010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__300 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__300 <b 3241) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__302 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3241
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let S := (BitVec.slice __opcode 20 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Rd := (BitVec.slice __opcode 12 4)
                                              let imm5 := (BitVec.slice __opcode 7 5)
                                              let stype := (BitVec.slice __opcode 5 2)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_SUB_r_A1enc_A_txt cond S Rn Rd
                                                imm5 stype Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__305 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                         __opcode 27 21)) == (0b0000010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__303 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__303 <b 3244) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__305 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3244
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let S := (BitVec.slice __opcode 20 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                  let Rs := (BitVec.slice __opcode 8 4)
                                                  let stype := (BitVec.slice __opcode 5 2)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_SUB_rr_A1enc_A_txt cond S
                                                    Rn Rd Rs stype Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__308 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                             __opcode 27 21)) == (0b0010010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 19 16)) == (0xD#4 : (BitVec 4)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__306 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__306 <b 3245) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__308 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3245
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let S := (BitVec.slice __opcode 20 1)
                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                      let imm12 := (BitVec.slice __opcode 0 12)
                                                      (decode_aarch32_instrs_SUB_SP_i_A1enc_A_txt
                                                        cond S Rd imm12)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__311 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                 __opcode 27 21)) == (0b0000010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 19 16)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__309 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__309 <b 3249) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__311 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3249
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let S := (BitVec.slice __opcode 20 1)
                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                          let imm5 := (BitVec.slice __opcode 7 5)
                                                          let stype := (BitVec.slice __opcode 5 2)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_SUB_SP_r_A1enc_A_txt
                                                            cond S Rd imm5 stype Rm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__314 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 27 20)) == (0x33#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 15 12)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__312 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__312 <b 3268) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__314 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3268
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let imm12 :=
                                                                (BitVec.slice __opcode 0 12)
                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 15)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_TEQ_i_A1enc_A_txt
                                                                    cond Rn imm12))
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__317 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 27 20)) == (0x13#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 15 12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__315 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__315 <b 3270) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__317 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3270
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let imm5 :=
                                                                    (BitVec.slice __opcode 7 5)
                                                                  let stype :=
                                                                    (BitVec.slice __opcode 5 2)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 15)])) != 0#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_TEQ_r_A1enc_A_txt
                                                                        cond Rn imm5 stype Rm))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__320 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 27 20)) == (0x13#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 15 12)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__318 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__318 <b 3272) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__320 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3272
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rs :=
                                                                        (BitVec.slice __opcode 8 4)
                                                                      let stype :=
                                                                        (BitVec.slice __opcode 5 2)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 15)])) != 0#1)) : Bool)
                                                                      then
                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                          ()))
                                                                      else
                                                                        (do
                                                                          (decode_aarch32_instrs_TEQ_rr_A1enc_A_txt
                                                                            cond Rn Rs stype Rm))
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__323 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 27 20)) == (0x31#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 12)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__321 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__321 <b 3273) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__323 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3273
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let imm12 :=
                                                                            (BitVec.slice __opcode 0
                                                                              12)
                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 15)])) != 0#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_TST_i_A1enc_A_txt
                                                                                cond Rn imm12))
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__326 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 27 20)) == (0x11#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__324 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__324 <b 3275) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__326 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3275
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let imm5 :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 5)
                                                                              let stype :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 2)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 15)])) != 0#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_TST_r_A1enc_A_txt
                                                                                    cond Rn imm5
                                                                                    stype Rm))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__329 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 27
                                                                                         20)) == (0x11#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 12)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__327 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__327 <b 3278) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__329 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3278
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let stype :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 2)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             15)])) != 0#1)) : Bool)
                                                                                  then
                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                      ()))
                                                                                  else
                                                                                    (do
                                                                                      (decode_aarch32_instrs_TST_rr_A1enc_A_txt
                                                                                        cond Rn Rs
                                                                                        stype Rm))
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__332 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 20)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             7 4)) == (0x9#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__330 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__330 <b 3304) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__332 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3304
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let RdHi :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let RdLo :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          4)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_UMAAL_A1enc_A_txt
                                                                                        cond RdHi
                                                                                        RdLo Rm Rn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__335 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 21)) == (0b0000101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 7 4)) == (0x9#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                   __opcode
                                                                                                   28
                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__333 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__333 <b 3306) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__335 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3306
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 1)
                                                                                          let RdHi :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let RdLo :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_UMLAL_A1enc_A_txt
                                                                                            cond S
                                                                                            RdHi
                                                                                            RdLo Rm
                                                                                            Rn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__338 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     27
                                                                                                     21)) == (0b0000100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     7
                                                                                                     4)) == (0x9#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                       __opcode
                                                                                                       28
                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__336 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__336 <b 3308) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__338 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3308
                                                                                              let cond :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  28
                                                                                                  4)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  20
                                                                                                  1)
                                                                                              let RdHi :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let RdLo :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  4)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_UMULL_A1enc_A_txt
                                                                                                cond
                                                                                                S
                                                                                                RdHi
                                                                                                RdLo
                                                                                                Rm
                                                                                                Rn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__341 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       27
                                                                                                       0)) == (0x320F002#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__339 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__339 <b 3760) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__341 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3760
                                                                                                  let cond :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      4)
                                                                                                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                      (decode_aarch32_instrs_WFE_A1enc_A_txt
                                                                                                        cond))
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__344 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           27
                                                                                                           0)) == (0x320F003#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                               __opcode
                                                                                                               28
                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__342 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__342 <b 3763) : Bool))))
                                                                                                        else
                                                                                                          (pure false))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__344 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3763
                                                                                                      let cond :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          4)
                                                                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                          (decode_aarch32_instrs_WFI_A1enc_A_txt
                                                                                                            cond))
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__347 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               27
                                                                                                               0)) == (0x320F001#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                   __opcode
                                                                                                                   28
                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__345 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__345 <b 3766) : Bool))))
                                                                                                            else
                                                                                                              (pure false))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__347 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3766
                                                                                                          let cond :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
                                                                                                              4)
                                                                                                          if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                              (decode_aarch32_instrs_YIELD_A1enc_A_txt
                                                                                                                cond))
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__350 ← (( do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   27
                                                                                                                   0)) == (0x160006E#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                       __opcode
                                                                                                                       28
                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__348 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__348 <b 3772) : Bool))))
                                                                                                                else
                                                                                                                  (pure false))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__350 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3772
                                                                                                              let cond :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  28
                                                                                                                  4)
                                                                                                              if ((((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                     __opcode
                                                                                                                                                     9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         15)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       16)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 19)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         3)])) != 0#1)) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_aarch32_instrs_ERET_A1enc_A_txt
                                                                                                                    cond))
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__353 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         27
                                                                                                                         20)) == (0x14#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         7
                                                                                                                         4)) == (0x7#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                           __opcode
                                                                                                                           28
                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__351 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__351 <b 3774) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__353 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3774
                                                                                                                  let cond :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      28
                                                                                                                      4)
                                                                                                                  let imm12 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      12)
                                                                                                                  let imm4 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_aarch32_instrs_HVC_A1enc_A_txt
                                                                                                                    cond
                                                                                                                    imm12
                                                                                                                    imm4)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__356 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             27
                                                                                                                             23)) == (0b00010#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               16)) == (0b001111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               0)) == (0x000#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                               __opcode
                                                                                                                               28
                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__354 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__354 <b 3778) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__356 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3778
                                                                                                                      let cond :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          28
                                                                                                                          4)
                                                                                                                      let R :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let Rd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      if (((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                   __opcode
                                                                                                                                                   17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                 __opcode
                                                                                                                                                 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                                          (decode_aarch32_instrs_MRS_A1enc_AS_txt
                                                                                                                            cond
                                                                                                                            R
                                                                                                                            Rd))
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (pure true)))))))))))))))))))))))))))))


end ArmFull.Functions
