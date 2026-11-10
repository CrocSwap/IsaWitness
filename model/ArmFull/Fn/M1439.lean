import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0230
import ArmFull.Fn.M0231
import ArmFull.Fn.M0232
import ArmFull.Fn.M0233
import ArmFull.Fn.M0838
import ArmFull.Fn.M0839
import ArmFull.Fn.M1283

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
def __DecodeA32_DataProMisc__seg2 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__179 ← (( do
    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x34#8 : (BitVec 8))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__177 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__177 <b 3021) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__179 : Bool)
  then
    (do
      writeReg SEE 3021
      let cond := (BitVec.slice __opcode 28 4)
      let imm4 := (BitVec.slice __opcode 16 4)
      let Rd := (BitVec.slice __opcode 12 4)
      let imm12 := (BitVec.slice __opcode 0 12)
      (decode_aarch32_instrs_MOVT_A1enc_A_txt cond imm4 Rd imm12)
      (pure false))
  else
    (do
      let w__182 ← (( do
        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 15 12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 7 4)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__180 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__180 <b 3027) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__182 : Bool)
      then
        (do
          writeReg SEE 3027
          let cond := (BitVec.slice __opcode 28 4)
          let S := (BitVec.slice __opcode 20 1)
          let Rd := (BitVec.slice __opcode 16 4)
          let Rm := (BitVec.slice __opcode 8 4)
          let Rn := (BitVec.slice __opcode 0 4)
          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 15)])) != 0#1)) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_aarch32_instrs_MUL_A1enc_A_txt cond S Rd Rm Rn))
          (pure false))
      else
        (do
          let w__185 ← (( do
            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0011111#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 19 16)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__183 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__183 <b 3030) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__185 : Bool)
          then
            (do
              writeReg SEE 3030
              let cond := (BitVec.slice __opcode 28 4)
              let S := (BitVec.slice __opcode 20 1)
              let Rd := (BitVec.slice __opcode 12 4)
              let imm12 := (BitVec.slice __opcode 0 12)
              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 19)])) != 0#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_MVN_i_A1enc_A_txt cond S Rd imm12))
              (pure false))
          else
            (do
              let w__188 ← (( do
                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0001111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 19 16)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__186 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__186 <b 3032) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__188 : Bool)
              then
                (do
                  writeReg SEE 3032
                  let cond := (BitVec.slice __opcode 28 4)
                  let S := (BitVec.slice __opcode 20 1)
                  let Rd := (BitVec.slice __opcode 12 4)
                  let imm5 := (BitVec.slice __opcode 7 5)
                  let stype := (BitVec.slice __opcode 5 2)
                  let Rm := (BitVec.slice __opcode 0 4)
                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 19)])) != 0#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_MVN_r_A1enc_A_txt cond S Rd imm5 stype Rm))
                  (pure false))
              else
                (do
                  let w__191 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0001111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 19 16)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__189 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__189 <b 3035) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__191 : Bool)
                  then
                    (do
                      writeReg SEE 3035
                      let cond := (BitVec.slice __opcode 28 4)
                      let S := (BitVec.slice __opcode 20 1)
                      let Rd := (BitVec.slice __opcode 12 4)
                      let Rs := (BitVec.slice __opcode 8 4)
                      let stype := (BitVec.slice __opcode 5 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 19)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_MVN_rr_A1enc_A_txt cond S Rd Rs stype Rm))
                      (pure false))
                  else
                    (do
                      let w__194 ← (( do
                        if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb __opcode 27 0)) == (0x320F000#28 : (BitVec 28))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__192 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__192 <b 3036) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__194 : Bool)
                      then
                        (do
                          writeReg SEE 3036
                          let cond := (BitVec.slice __opcode 28 4)
                          if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 0#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_NOP_A1enc_A_txt cond))
                          (pure false))
                      else
                        (do
                          let w__197 ← (( do
                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode
                                   27 21)) == (0b0011100#7 : (BitVec 7))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__195 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__195 <b 3041) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__197 : Bool)
                          then
                            (do
                              writeReg SEE 3041
                              let cond := (BitVec.slice __opcode 28 4)
                              let S := (BitVec.slice __opcode 20 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rd := (BitVec.slice __opcode 12 4)
                              let imm12 := (BitVec.slice __opcode 0 12)
                              (decode_aarch32_instrs_ORR_i_A1enc_A_txt cond S Rn Rd imm12)
                              (pure false))
                          else
                            (do
                              let w__200 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                         __opcode 27 21)) == (0b0001100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__198 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__198 <b 3043) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__200 : Bool)
                              then
                                (do
                                  writeReg SEE 3043
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let S := (BitVec.slice __opcode 20 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rd := (BitVec.slice __opcode 12 4)
                                  let imm5 := (BitVec.slice __opcode 7 5)
                                  let stype := (BitVec.slice __opcode 5 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_ORR_r_A1enc_A_txt cond S Rn Rd imm5 stype
                                    Rm)
                                  (pure false))
                              else
                                (do
                                  let w__203 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                             __opcode 27 21)) == (0b0001100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__201 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__201 <b 3046) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__203 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3046
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let S := (BitVec.slice __opcode 20 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rd := (BitVec.slice __opcode 12 4)
                                      let Rs := (BitVec.slice __opcode 8 4)
                                      let stype := (BitVec.slice __opcode 5 2)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_ORR_rr_A1enc_A_txt cond S Rn Rd Rs
                                        stype Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__206 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 27 20)) == (0x10#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 11 4)) == (0x05#8 : (BitVec 8)))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__204 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__204 <b 3068) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__206 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3068
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rd := (BitVec.slice __opcode 12 4)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 11)])) != 0#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_QADD_A1enc_A_txt cond Rn Rd Rm))
                                          (pure false))
                                      else
                                        (do
                                          let w__209 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 27 20)) == (0x14#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 11 4)) == (0x05#8 : (BitVec 8)))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__207 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__207 <b 3072) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__209 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3072
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Rd := (BitVec.slice __opcode 12 4)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 11)])) != 0#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_QDADD_A1enc_A_txt cond Rn
                                                    Rd Rm))
                                              (pure false))
                                          else
                                            (do
                                              let w__212 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 27 20)) == (0x16#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 11 4)) == (0x05#8 : (BitVec 8)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__210 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__210 <b 3074) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__212 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3074
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 11)])) != 0#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_QDSUB_A1enc_A_txt cond
                                                        Rn Rd Rm))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__215 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 27 20)) == (0x12#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 11 4)) == (0x05#8 : (BitVec 8)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__213 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__213 <b 3082) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__215 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3082
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 11)])) != 0#1)) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_QSUB_A1enc_A_txt
                                                            cond Rn Rd Rm))
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__218 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                               __opcode 27 21)) == (0b0010011#7 : (BitVec 7))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__216 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__216 <b 3096) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__218 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3096
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let S := (BitVec.slice __opcode 20 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                          let imm12 := (BitVec.slice __opcode 0 12)
                                                          (decode_aarch32_instrs_RSB_i_A1enc_A_txt
                                                            cond S Rn Rd imm12)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__221 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                     __opcode 27 21)) == (0b0000011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__219 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__219 <b 3099) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__221 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3099
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              let S := (BitVec.slice __opcode 20 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                              let imm5 :=
                                                                (BitVec.slice __opcode 7 5)
                                                              let stype :=
                                                                (BitVec.slice __opcode 5 2)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_RSB_r_A1enc_A_txt
                                                                cond S Rn Rd imm5 stype Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__224 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                         __opcode 27 21)) == (0b0000011#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__222 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__222 <b 3101) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__224 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3101
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 20 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 8 4)
                                                                  let stype :=
                                                                    (BitVec.slice __opcode 5 2)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_RSB_rr_A1enc_A_txt
                                                                    cond S Rn Rd Rs stype Rm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__227 ← (( do
                                                                    if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                           __opcode 27 21)) == (0b0010111#7 : (BitVec 7))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__225 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__225 <b 3102) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__227 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3102
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 20 1)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let imm12 :=
                                                                        (BitVec.slice __opcode 0 12)
                                                                      (decode_aarch32_instrs_RSC_i_A1enc_A_txt
                                                                        cond S Rn Rd imm12)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__230 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                 __opcode 27 21)) == (0b0000111#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__228 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__228 <b 3103) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__230 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3103
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let imm5 :=
                                                                            (BitVec.slice __opcode 7
                                                                              5)
                                                                          let stype :=
                                                                            (BitVec.slice __opcode 5
                                                                              2)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_RSC_r_A1enc_A_txt
                                                                            cond S Rn Rd imm5 stype
                                                                            Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__233 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                     __opcode 27 21)) == (0b0000111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__231 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__231 <b 3104) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__233 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3104
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 20 1)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 4)
                                                                              let stype :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 2)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_RSC_rr_A1enc_A_txt
                                                                                cond S Rn Rd Rs
                                                                                stype Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__236 ← (( do
                                                                                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                       __opcode 27
                                                                                       21)) == (0b0010110#7 : (BitVec 7))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__234 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__234 <b 3113) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__236 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3113
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let imm12 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 12)
                                                                                  (decode_aarch32_instrs_SBC_i_A1enc_A_txt
                                                                                    cond S Rn Rd
                                                                                    imm12)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__239 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 21)) == (0b0000110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__237 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__237 <b 3115) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__239 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3115
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let imm5 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          5)
                                                                                      let stype :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          2)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_SBC_r_A1enc_A_txt
                                                                                        cond S Rn Rd
                                                                                        imm5 stype
                                                                                        Rm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__242 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 21)) == (0b0000110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   7
                                                                                                   7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
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
                                                                                                let w__240 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__240 <b 3118) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__242 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3118
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          let stype :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 2)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_SBC_rr_A1enc_A_txt
                                                                                            cond S
                                                                                            Rn Rd Rs
                                                                                            stype Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__245 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   27
                                                                                                   0)) == (0x320F004#28 : (BitVec 28))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                       __opcode
                                                                                                       28
                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__243 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__243 <b 3127) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__245 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3127
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
                                                                                                  (decode_aarch32_instrs_SEV_A1enc_A_txt
                                                                                                    cond))
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__248 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         27
                                                                                                         20)) == (0x10#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           7
                                                                                                           7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__246 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__246 <b 3142) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__248 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3142
                                                                                                  let cond :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      4)
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Ra :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let M :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      1)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      1)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_SMLABB_A1enc_A_txt
                                                                                                    cond
                                                                                                    Rd
                                                                                                    Ra
                                                                                                    Rm
                                                                                                    M
                                                                                                    N
                                                                                                    Rn)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__251 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             27
                                                                                                             21)) == (0b0000111#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
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
                                                                                                            let w__249 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__249 <b 3146) : Bool))))
                                                                                                        else
                                                                                                          (pure false))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__251 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3146
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
                                                                                                      (decode_aarch32_instrs_SMLAL_A1enc_A_txt
                                                                                                        cond
                                                                                                        S
                                                                                                        RdHi
                                                                                                        RdLo
                                                                                                        Rm
                                                                                                        Rn)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__254 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 27
                                                                                                                 20)) == (0x14#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   7
                                                                                                                   7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                   __opcode
                                                                                                                   28
                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__252 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__252 <b 3148) : Bool))))
                                                                                                            else
                                                                                                              (pure false))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__254 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3148
                                                                                                          let cond :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
                                                                                                              4)
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
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              6
                                                                                                              1)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_SMLALBB_A1enc_A_txt
                                                                                                            cond
                                                                                                            RdHi
                                                                                                            RdLo
                                                                                                            Rm
                                                                                                            M
                                                                                                            N
                                                                                                            Rn)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__257 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     27
                                                                                                                     20)) == (0x12#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       7
                                                                                                                       7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       5
                                                                                                                       4)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                       __opcode
                                                                                                                       28
                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__255 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__255 <b 3152) : Bool))))
                                                                                                                else
                                                                                                                  (pure false))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__257 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3152
                                                                                                              let cond :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  28
                                                                                                                  4)
                                                                                                              let Rd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Ra :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              let M :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  6
                                                                                                                  1)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_SMLAWB_A1enc_A_txt
                                                                                                                cond
                                                                                                                Rd
                                                                                                                Ra
                                                                                                                Rm
                                                                                                                M
                                                                                                                Rn)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__260 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         27
                                                                                                                         20)) == (0x16#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           12)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             7
                                                                                                                             7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
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
                                                                                                                        let w__258 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__258 <b 3166) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__260 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3166
                                                                                                                  let cond :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      28
                                                                                                                      4)
                                                                                                                  let Rd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      4)
                                                                                                                  let M :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      6
                                                                                                                      1)
                                                                                                                  let N :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      1)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
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
                                                                                                                      (decode_aarch32_instrs_SMULBB_A1enc_A_txt
                                                                                                                        cond
                                                                                                                        Rd
                                                                                                                        Rm
                                                                                                                        M
                                                                                                                        N
                                                                                                                        Rn))
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__263 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             27
                                                                                                                             21)) == (0b0000110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
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
                                                                                                                            let w__261 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__261 <b 3168) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__263 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3168
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
                                                                                                                      (decode_aarch32_instrs_SMULL_A1enc_A_txt
                                                                                                                        cond
                                                                                                                        S
                                                                                                                        RdHi
                                                                                                                        RdLo
                                                                                                                        Rm
                                                                                                                        Rn)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__266 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 27
                                                                                                                                 20)) == (0x12#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   12)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     7
                                                                                                                                     7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     5
                                                                                                                                     4)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                   __opcode
                                                                                                                                   28
                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__264 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__264 <b 3170) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__266 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3170
                                                                                                                          let cond :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              28
                                                                                                                              4)
                                                                                                                          let Rd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              4)
                                                                                                                          let M :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              1)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
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
                                                                                                                              (decode_aarch32_instrs_SMULWB_A1enc_A_txt
                                                                                                                                cond
                                                                                                                                Rd
                                                                                                                                Rm
                                                                                                                                M
                                                                                                                                Rn))
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__269 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     27
                                                                                                                                     25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       22
                                                                                                                                       22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         20
                                                                                                                                         20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         7
                                                                                                                                         4)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                       __opcode
                                                                                                                                       28
                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__267 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__267 <b 3203) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__269 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3203
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
                                                                                                                              let Rt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let imm4H :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  4)
                                                                                                                              let imm4L :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_aarch32_instrs_STRD_i_A1enc_A_txt
                                                                                                                                cond
                                                                                                                                P
                                                                                                                                U
                                                                                                                                W
                                                                                                                                Rn
                                                                                                                                Rt
                                                                                                                                imm4H
                                                                                                                                imm4L)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (pure true)))))))))))))))))))))))))))))))


end ArmFull.Functions
