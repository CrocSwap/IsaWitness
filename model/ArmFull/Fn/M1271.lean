import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0192
import ArmFull.Fn.M0202
import ArmFull.Fn.M0230
import ArmFull.Fn.M0240
import ArmFull.Fn.M1047
import ArmFull.Fn.M1048
import ArmFull.Fn.M1089
import ArmFull.Fn.M1143

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
def __DecodeA32_Unconditional__seg0 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1 ← (( do
    if (((__opcode == 0b11110101011111111111000000011111#32) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 2879) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 2879
      if ((((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 __opcode 3)])) != 1#1)) : Bool)
      then sailThrow ((Error_ConstrainedUnpredictable ()))
      else
        (do
          (decode_aarch32_instrs_CLREX_A1enc_A_txt ()))
      (pure false))
  else
    (do
      let w__3 ← (( do
        if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb __opcode 31 4)) == (0xF57FF05#28 : (BitVec 28))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 2899) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 2899
          let option_name := (BitVec.slice __opcode 0 4)
          if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
              (decode_aarch32_instrs_DMB_A1enc_A_txt option_name))
          (pure false))
      else
        (do
          let w__5 ← (( do
            if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb __opcode 31 4)) == (0xF57FF04#28 : (BitVec 28))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 2901) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 2901
              let option_name := (BitVec.slice __opcode 0 4)
              if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                  (decode_aarch32_instrs_DSB_A1enc_A_txt option_name))
              (pure false))
          else
            (do
              let w__7 ← (( do
                if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb __opcode 31 4)) == (0xF57FF06#28 : (BitVec 28))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 2909) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 2909
                  let option_name := (BitVec.slice __opcode 0 4)
                  if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                      (decode_aarch32_instrs_ISB_A1enc_A_txt option_name))
                  (pure false))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xF5#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 21 20)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 15 12)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 3049) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 3049
                      let U := (BitVec.slice __opcode 23 1)
                      let R := (BitVec.slice __opcode 22 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let imm12 := (BitVec.slice __opcode 0 12)
                      (decode_aarch32_instrs_PLD_i_A1enc_A_txt U R Rn imm12)
                      (pure false))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0xF5#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                 __opcode 22 12)) == (0b10111111111#11 : (BitVec 11)))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 3052) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 3052
                          let U := (BitVec.slice __opcode 23 1)
                          let imm12 := (BitVec.slice __opcode 0 12)
                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 22)])) != 1#1) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_PLD_l_A1enc_A_txt U imm12))
                          (pure false))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0xF7#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 3054) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 3054
                              let U := (BitVec.slice __opcode 23 1)
                              let R := (BitVec.slice __opcode 22 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let imm5 := (BitVec.slice __opcode 7 5)
                              let stype := (BitVec.slice __opcode 5 2)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_PLD_r_A1enc_A_txt U R Rn imm5 stype Rm)
                              (pure false))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0xF4#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 22 20)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 15 12)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 3056) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 3056
                                  let U := (BitVec.slice __opcode 23 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let imm12 := (BitVec.slice __opcode 0 12)
                                  (decode_aarch32_instrs_PLI_i_A1enc_A_txt U Rn imm12)
                                  (pure false))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0xF6#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 22 20)) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 3060) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3060
                                      let U := (BitVec.slice __opcode 23 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let imm5 := (BitVec.slice __opcode 7 5)
                                      let stype := (BitVec.slice __opcode 5 2)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_PLI_r_A1enc_A_txt U Rn imm5 stype Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if (((__opcode == 0b11110101011111111111000001110000#32) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 3111) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3111
                                          if ((((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 3)])) != 0#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_SB_A1enc_A_txt ()))
                                          (pure false))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                     __opcode 31 10)) == (0b1111000100000001000000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 8 0)) == (0b000000000#9 : (BitVec 9)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 3125) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3125
                                              let E := (BitVec.slice __opcode 9 1)
                                              if (((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 10)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 15)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 3)])) != 0#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_SETEND_A1enc_A_txt E))
                                              (pure false))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                         __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 11 8)) == (0x7#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 3350) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3350
                                                  let U := (BitVec.slice __opcode 24 1)
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 20 2)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VABA_A1enc_A_txt U D size
                                                    Vn Vd N Q M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                             __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 11 8)) == (0x5#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 3351) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3351
                                                      let U := (BitVec.slice __opcode 24 1)
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let size := (BitVec.slice __opcode 20 2)
                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let N := (BitVec.slice __opcode 7 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VABA_A2enc_A_txt U D
                                                        size Vn Vd N M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 11 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 3354) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3354
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let sz := (BitVec.slice __opcode 20 1)
                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let N := (BitVec.slice __opcode 7 1)
                                                          let Q := (BitVec.slice __opcode 6 1)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VABD_f_A1enc_A_txt
                                                            D sz Vn Vd N Q M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                     __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 11 8)) == (0x7#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 3356) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3356
                                                              let U := (BitVec.slice __opcode 24 1)
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 20 2)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              let Q := (BitVec.slice __opcode 6 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VABD_i_A1enc_A_txt
                                                                U D size Vn Vd N Q M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                         __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 11 8)) == (0x7#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 3357) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3357
                                                                  let U :=
                                                                    (BitVec.slice __opcode 24 1)
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 20 2)
                                                                  let Vn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 7 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VABD_i_A2enc_A_txt
                                                                    U D size Vn Vd N M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 9 7)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 3360) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3360
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 18 2)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let F :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 6 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VABS_A1enc_A_txt
                                                                        D size Vd F Q M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 3364) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3364
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let op :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Vn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 7
                                                                              1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode 6
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Vm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VACGE_A1enc_A_txt
                                                                            D op sz Vn Vd N Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 3366) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3366
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let sz :=
                                                                                (BitVec.slice
                                                                                  __opcode 20 1)
                                                                              let Vn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let N :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VADD_f_A1enc_A_txt
                                                                                D sz Vn Vd N Q M Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111100101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 8)) == (0x4#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 3370) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3370
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 2)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VADDHN_A1enc_A_txt
                                                                                    D size Vn Vd N M
                                                                                    Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 3372) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3372
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 2)
                                                                                      let Vn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode 6
                                                                                          1)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VADD_i_A1enc_A_txt
                                                                                        D size Vn Vd
                                                                                        N Q M Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   23
                                                                                                   23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     9)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       6
                                                                                                       6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 3374) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3374
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              24 1)
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 2)
                                                                                          let Vn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let op :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 1)
                                                                                          let N :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              7 1)
                                                                                          let M :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 1)
                                                                                          let Vm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VADDL_A1enc_A_txt
                                                                                            U D size
                                                                                            Vn Vd op
                                                                                            N M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 3376) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3376
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
                                                                                              (decode_aarch32_instrs_VAND_r_A1enc_A_txt
                                                                                                D Vn
                                                                                                Vd N
                                                                                                Q M
                                                                                                Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__47 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           23
                                                                                                           23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             21
                                                                                                             19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 8
                                                                                                                 7)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 5
                                                                                                                 4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__46 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__46 <b 3378) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__47 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3378
                                                                                                  let i :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      24
                                                                                                      1)
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let imm3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      3)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let cmode :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      1)
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VBIC_i_A1enc_A_txt
                                                                                                    i
                                                                                                    D
                                                                                                    imm3
                                                                                                    Vd
                                                                                                    cmode
                                                                                                    Q
                                                                                                    imm4)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__49 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               23
                                                                                                               23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 21
                                                                                                                 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     8
                                                                                                                     7)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     5
                                                                                                                     4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__48 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__48 <b 3379) : Bool))))
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
                                                                                                      writeReg SEE 3379
                                                                                                      let i :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          24
                                                                                                          1)
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let imm3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          3)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let cmode :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          4)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          1)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VBIC_i_A2enc_A_txt
                                                                                                        i
                                                                                                        D
                                                                                                        imm3
                                                                                                        Vd
                                                                                                        cmode
                                                                                                        Q
                                                                                                        imm4)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__51 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__50 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__50 <b 3382) : Bool))))
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
                                                                                                          writeReg SEE 3382
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
                                                                                                          (decode_aarch32_instrs_VBIC_r_A1enc_A_txt
                                                                                                            D
                                                                                                            Vn
                                                                                                            Vd
                                                                                                            N
                                                                                                            Q
                                                                                                            M
                                                                                                            Vm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__53 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__52 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__52 <b 3384) : Bool))))
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
                                                                                                              writeReg SEE 3384
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let op :=
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
                                                                                                              (decode_aarch32_instrs_VBIF_A1enc_A_txt
                                                                                                                D
                                                                                                                op
                                                                                                                Vn
                                                                                                                Vd
                                                                                                                N
                                                                                                                Q
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__55 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             17
                                                                                                                             16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 9
                                                                                                                                 7)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__54 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__54 <b 3386) : Bool))))
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
                                                                                                                  writeReg SEE 3386
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      18
                                                                                                                      2)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let F :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
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
                                                                                                                  (decode_aarch32_instrs_VCEQ_i_A1enc_A_txt
                                                                                                                    D
                                                                                                                    size
                                                                                                                    Vd
                                                                                                                    F
                                                                                                                    Q
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (pure true))))))))))))))))))))))))))))


end ArmFull.Functions
