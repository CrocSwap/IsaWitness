import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0230
import ArmFull.Fn.M0838
import ArmFull.Fn.M1008
import ArmFull.Fn.M1073
import ArmFull.Fn.M1280
import ArmFull.Fn.M1281
import ArmFull.Fn.M1282
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
def __DecodeT32__seg1 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__72 ← (( do
    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1110100010#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
             __opcode 20 20)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
    then
      (do
        let w__71 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__71 <b 2918) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__72 : Bool)
  then
    (do
      writeReg SEE 2918
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let P := (BitVec.slice __opcode 15 1)
      let M := (BitVec.slice __opcode 14 1)
      let register_list := (BitVec.slice __opcode 0 14)
      (decode_aarch32_instrs_LDM_T2enc_A_txt W Rn P M register_list)
      (pure false))
  else
    (do
      let w__74 ← (( do
        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1110100100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 20 20)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
        then
          (do
            let w__73 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__73 <b 2921) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__74 : Bool)
      then
        (do
          writeReg SEE 2921
          let W := (BitVec.slice __opcode 21 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let P := (BitVec.slice __opcode 15 1)
          let M := (BitVec.slice __opcode 14 1)
          let register_list := (BitVec.slice __opcode 0 14)
          (decode_aarch32_instrs_LDMDB_T1enc_A_txt W Rn P M register_list)
          (pure false))
      else
        (do
          let w__76 ← (( do
            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xF89#12 : (BitVec 12))) : Bool) : Bool)
            then
              (do
                let w__75 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__75 <b 2925) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__76 : Bool)
          then
            (do
              writeReg SEE 2925
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let imm12 := (BitVec.slice __opcode 0 12)
              (decode_aarch32_instrs_LDRB_i_T2enc_A_txt Rn Rt imm12)
              (pure false))
          else
            (do
              let w__78 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xF81#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 11 11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                then
                  (do
                    let w__77 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__77 <b 2926) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__78 : Bool)
              then
                (do
                  writeReg SEE 2926
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let P := (BitVec.slice __opcode 10 1)
                  let U := (BitVec.slice __opcode 9 1)
                  let W := (BitVec.slice __opcode 8 1)
                  let imm8 := (BitVec.slice __opcode 0 8)
                  (decode_aarch32_instrs_LDRB_i_T3enc_A_txt Rn Rt P U W imm8)
                  (pure false))
              else
                (do
                  let w__80 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xF8#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                             __opcode 22 16)) == (0b0011111#7 : (BitVec 7)))) : Bool) : Bool)
                    then
                      (do
                        let w__79 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__79 <b 2928) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__80 : Bool)
                  then
                    (do
                      writeReg SEE 2928
                      let U := (BitVec.slice __opcode 23 1)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let imm12 := (BitVec.slice __opcode 0 12)
                      (decode_aarch32_instrs_LDRB_l_T1enc_A_txt U Rt imm12)
                      (pure false))
                  else
                    (do
                      let w__82 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xF81#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                 __opcode 11 6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                        then
                          (do
                            let w__81 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__81 <b 2931) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__82 : Bool)
                      then
                        (do
                          writeReg SEE 2931
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let imm2 := (BitVec.slice __opcode 4 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_LDRB_r_T2enc_A_txt Rn Rt imm2 Rm)
                          (pure false))
                      else
                        (do
                          let w__84 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xF81#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 11 8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                            then
                              (do
                                let w__83 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__83 <b 2934) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__84 : Bool)
                          then
                            (do
                              writeReg SEE 2934
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let imm8 := (BitVec.slice __opcode 0 8)
                              (decode_aarch32_instrs_LDRBT_T1enc_A_txt Rn Rt imm8)
                              (pure false))
                          else
                            (do
                              let w__86 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                         __opcode 31 25)) == (0b1110100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 22 22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 20 20)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__85 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__85 <b 2936) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__86 : Bool)
                              then
                                (do
                                  writeReg SEE 2936
                                  let P := (BitVec.slice __opcode 24 1)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let W := (BitVec.slice __opcode 21 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let Rt2 := (BitVec.slice __opcode 8 4)
                                  let imm8 := (BitVec.slice __opcode 0 8)
                                  (decode_aarch32_instrs_LDRD_i_T1enc_A_txt P U W Rn Rt Rt2 imm8)
                                  (pure false))
                              else
                                (do
                                  let w__88 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                             __opcode 31 25)) == (0b1110100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 22 22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                               __opcode 20 16)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__87 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__87 <b 2938) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__88 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2938
                                      let P := (BitVec.slice __opcode 24 1)
                                      let U := (BitVec.slice __opcode 23 1)
                                      let W := (BitVec.slice __opcode 21 1)
                                      let Rt := (BitVec.slice __opcode 12 4)
                                      let Rt2 := (BitVec.slice __opcode 8 4)
                                      let imm8 := (BitVec.slice __opcode 0 8)
                                      (decode_aarch32_instrs_LDRD_l_T1enc_A_txt P U W Rt Rt2 imm8)
                                      (pure false))
                                  else
                                    (do
                                      let w__90 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xE85#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 11 8)) == (0xF#4 : (BitVec 4)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__89 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__89 <b 2941) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__90 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2941
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rt := (BitVec.slice __opcode 12 4)
                                          let imm8 := (BitVec.slice __opcode 0 8)
                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 11)])) != 1#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_LDREX_T1enc_A_txt Rn Rt imm8))
                                          (pure false))
                                      else
                                        (do
                                          let w__92 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 11 0)) == (0xF4F#12 : (BitVec 12)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__91 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__91 <b 2943) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__92 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2943
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Rt := (BitVec.slice __opcode 12 4)
                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 3)])) != 1#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_LDREXB_T1enc_A_txt Rn Rt))
                                              (pure false))
                                          else
                                            (do
                                              let w__94 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 7 0)) == (0x7F#8 : (BitVec 8)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__93 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__93 <b 2945) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__94 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2945
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Rt := (BitVec.slice __opcode 12 4)
                                                  let Rt2 := (BitVec.slice __opcode 8 4)
                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 0)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 3)])) != 1#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_LDREXD_T1enc_A_txt Rn
                                                        Rt Rt2))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__96 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 11 0)) == (0xF5F#12 : (BitVec 12)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__95 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__95 <b 2947) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__96 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2947
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Rt := (BitVec.slice __opcode 12 4)
                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 3)])) != 1#1)) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_LDREXH_T1enc_A_txt
                                                            Rn Rt))
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__98 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                               __opcode 31 20)) == (0xF8B#12 : (BitVec 12))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__97 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__97 <b 2950) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__98 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2950
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rt := (BitVec.slice __opcode 12 4)
                                                          let imm12 := (BitVec.slice __opcode 0 12)
                                                          (decode_aarch32_instrs_LDRH_i_T2enc_A_txt
                                                            Rn Rt imm12)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__100 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xF83#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 11 11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__99 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__99 <b 2951) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__100 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2951
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Rt := (BitVec.slice __opcode 12 4)
                                                              let P := (BitVec.slice __opcode 10 1)
                                                              let U := (BitVec.slice __opcode 9 1)
                                                              let W := (BitVec.slice __opcode 8 1)
                                                              let imm8 :=
                                                                (BitVec.slice __opcode 0 8)
                                                              (decode_aarch32_instrs_LDRH_i_T3enc_A_txt
                                                                Rn Rt P U W imm8)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__102 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0xF8#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                         __opcode 22 16)) == (0b0111111#7 : (BitVec 7)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__101 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__101 <b 2953) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__102 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2953
                                                                  let U :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let imm12 :=
                                                                    (BitVec.slice __opcode 0 12)
                                                                  (decode_aarch32_instrs_LDRH_l_T1enc_A_txt
                                                                    U Rt imm12)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__104 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xF83#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 11 6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__103 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__103 <b 2956) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__104 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2956
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let imm2 :=
                                                                        (BitVec.slice __opcode 4 2)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_LDRH_r_T2enc_A_txt
                                                                        Rn Rt imm2 Rm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__106 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xF83#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__105 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__105 <b 2959) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__106 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2959
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let imm8 :=
                                                                            (BitVec.slice __opcode 0
                                                                              8)
                                                                          (decode_aarch32_instrs_LDRHT_T1enc_A_txt
                                                                            Rn Rt imm8)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__108 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 31 20)) == (0xF8D#12 : (BitVec 12))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__107 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__107 <b 2963) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__108 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2963
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let imm12 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 12)
                                                                              (decode_aarch32_instrs_LDR_i_T3enc_A_txt
                                                                                Rn Rt imm12)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__110 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xF85#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__109 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__109 <b 2964) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__110 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2964
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let P :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 9 1)
                                                                                  let W :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 1)
                                                                                  let imm8 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 8)
                                                                                  (decode_aarch32_instrs_LDR_i_T4enc_A_txt
                                                                                    Rn Rt P U W imm8)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__112 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0xF8#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             22 16)) == (0b1011111#7 : (BitVec 7)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__111 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__111 <b 2967) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__112 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2967
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let imm12 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          12)
                                                                                      (decode_aarch32_instrs_LDR_l_T2enc_A_txt
                                                                                        U Rt imm12)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__114 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xF85#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__113 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__113 <b 2970) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__114 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2970
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let imm2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 2)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_LDR_r_T2enc_A_txt
                                                                                            Rn Rt
                                                                                            imm2 Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__116 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   31
                                                                                                   20)) == (0xF99#12 : (BitVec 12))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__115 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__115 <b 2972) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__116 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2972
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
                                                                                              let imm12 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  12)
                                                                                              (decode_aarch32_instrs_LDRSB_i_T1enc_A_txt
                                                                                                Rn
                                                                                                Rt
                                                                                                imm12)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__118 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xF91#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__117 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__117 <b 2973) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__118 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2973
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
                                                                                                  let P :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      1)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      9
                                                                                                      1)
                                                                                                  let W :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      1)
                                                                                                  let imm8 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      8)
                                                                                                  (decode_aarch32_instrs_LDRSB_i_T2enc_A_txt
                                                                                                    Rn
                                                                                                    Rt
                                                                                                    P
                                                                                                    U
                                                                                                    W
                                                                                                    imm8)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__120 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0xF9#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             22
                                                                                                             16)) == (0b0011111#7 : (BitVec 7)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__119 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__119 <b 2975) : Bool))))
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
                                                                                                      writeReg SEE 2975
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          23
                                                                                                          1)
                                                                                                      let Rt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let imm12 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          12)
                                                                                                      (decode_aarch32_instrs_LDRSB_l_T1enc_A_txt
                                                                                                        U
                                                                                                        Rt
                                                                                                        imm12)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__122 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xF91#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 11
                                                                                                                 6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__121 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__121 <b 2978) : Bool))))
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
                                                                                                          writeReg SEE 2978
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
                                                                                                          let imm2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              2)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_LDRSB_r_T2enc_A_txt
                                                                                                            Rn
                                                                                                            Rt
                                                                                                            imm2
                                                                                                            Rm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__124 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xF91#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__123 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__123 <b 2981) : Bool))))
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
                                                                                                              writeReg SEE 2981
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
                                                                                                              let imm8 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  8)
                                                                                                              (decode_aarch32_instrs_LDRSBT_T1enc_A_txt
                                                                                                                Rn
                                                                                                                Rt
                                                                                                                imm8)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__126 ← (( do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       31
                                                                                                                       20)) == (0xF9B#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__125 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__125 <b 2983) : Bool))))
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
                                                                                                                  writeReg SEE 2983
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
                                                                                                                  let imm12 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      12)
                                                                                                                  (decode_aarch32_instrs_LDRSH_i_T1enc_A_txt
                                                                                                                    Rn
                                                                                                                    Rt
                                                                                                                    imm12)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__128 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__127 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__127 <b 2984) : Bool))))
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
                                                                                                                      writeReg SEE 2984
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
                                                                                                                      let P :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          1)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          9
                                                                                                                          1)
                                                                                                                      let W :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          8
                                                                                                                          1)
                                                                                                                      let imm8 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          8)
                                                                                                                      (decode_aarch32_instrs_LDRSH_i_T2enc_A_txt
                                                                                                                        Rn
                                                                                                                        Rt
                                                                                                                        P
                                                                                                                        U
                                                                                                                        W
                                                                                                                        imm8)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__130 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0xF9#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 22
                                                                                                                                 16)) == (0b0111111#7 : (BitVec 7)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__129 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__129 <b 2986) : Bool))))
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
                                                                                                                          writeReg SEE 2986
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              23
                                                                                                                              1)
                                                                                                                          let Rt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let imm12 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              12)
                                                                                                                          (decode_aarch32_instrs_LDRSH_l_T1enc_A_txt
                                                                                                                            U
                                                                                                                            Rt
                                                                                                                            imm12)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__132 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__131 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__131 <b 2989) : Bool))))
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
                                                                                                                              writeReg SEE 2989
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
                                                                                                                              let imm2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  4
                                                                                                                                  2)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_aarch32_instrs_LDRSH_r_T2enc_A_txt
                                                                                                                                Rn
                                                                                                                                Rt
                                                                                                                                imm2
                                                                                                                                Rm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__134 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         11
                                                                                                                                         8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__133 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__133 <b 2992) : Bool))))
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
                                                                                                                                  writeReg SEE 2992
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
                                                                                                                                  let imm8 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      8)
                                                                                                                                  (decode_aarch32_instrs_LDRSHT_T1enc_A_txt
                                                                                                                                    Rn
                                                                                                                                    Rt
                                                                                                                                    imm8)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__136 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xF85#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             11
                                                                                                                                             8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__135 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__135 <b 2995) : Bool))))
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
                                                                                                                                      writeReg SEE 2995
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
                                                                                                                                      let imm8 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          8)
                                                                                                                                      (decode_aarch32_instrs_LDRT_T1enc_A_txt
                                                                                                                                        Rn
                                                                                                                                        Rt
                                                                                                                                        imm8)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__138 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b11111010000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   7
                                                                                                                                                   4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__137 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__137 <b 2998) : Bool))))
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
                                                                                                                                          writeReg SEE 2998
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
                                                                                                                                          (decode_aarch32_instrs_LSL_r_T2enc_A_txt
                                                                                                                                            S
                                                                                                                                            Rn
                                                                                                                                            Rd
                                                                                                                                            Rm)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__140 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0xEE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       20
                                                                                                                                                       20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         11
                                                                                                                                                         9)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         4
                                                                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__139 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__139 <b 3002) : Bool))))
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
                                                                                                                                              writeReg SEE 3002
                                                                                                                                              let opc1 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  21
                                                                                                                                                  3)
                                                                                                                                              let CRn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Rt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  4)
                                                                                                                                              let coproc :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  8
                                                                                                                                                  1)
                                                                                                                                              let opc2 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  3)
                                                                                                                                              let CRm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  4)
                                                                                                                                              (decode_aarch32_instrs_MCR_T1enc_A_txt
                                                                                                                                                opc1
                                                                                                                                                CRn
                                                                                                                                                Rt
                                                                                                                                                coproc
                                                                                                                                                opc2
                                                                                                                                                CRm)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__142 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xEC4#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         11
                                                                                                                                                         9)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__141 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__141 <b 3004) : Bool))))
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
                                                                                                                                                  writeReg SEE 3004
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
                                                                                                                                                  let coproc :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      8
                                                                                                                                                      1)
                                                                                                                                                  let opc1 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      4
                                                                                                                                                      4)
                                                                                                                                                  let CRm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_aarch32_instrs_MCRR_T1enc_A_txt
                                                                                                                                                    Rt2
                                                                                                                                                    Rt
                                                                                                                                                    coproc
                                                                                                                                                    opc1
                                                                                                                                                    CRm)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__144 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             20)) == (0xFB0#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             7
                                                                                                                                                             4)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__143 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__143 <b 3006) : Bool))))
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
                                                                                                                                                      writeReg SEE 3006
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
                                                                                                                                                      (decode_aarch32_instrs_MLA_T1enc_A_txt
                                                                                                                                                        Rn
                                                                                                                                                        Ra
                                                                                                                                                        Rd
                                                                                                                                                        Rm)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__146 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 20)) == (0xFB0#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 7
                                                                                                                                                                 4)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__145 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__145 <b 3008) : Bool))))
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
                                                                                                                                                          writeReg SEE 3008
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
                                                                                                                                                          (decode_aarch32_instrs_MLS_T1enc_A_txt
                                                                                                                                                            Rn
                                                                                                                                                            Ra
                                                                                                                                                            Rd
                                                                                                                                                            Rm)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__148 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       25
                                                                                                                                                                       21)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       19
                                                                                                                                                                       15)) == (0b11110#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__147 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__147 <b 3012) : Bool))))
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
                                                                                                                                                              writeReg SEE 3012
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
                                                                                                                                                              (decode_aarch32_instrs_MOV_i_T2enc_A_txt
                                                                                                                                                                i
                                                                                                                                                                S
                                                                                                                                                                imm3
                                                                                                                                                                Rd
                                                                                                                                                                imm8)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__150 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           25
                                                                                                                                                                           20)) == (0b100100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__149 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__149 <b 3013) : Bool))))
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
                                                                                                                                                                  writeReg SEE 3013
                                                                                                                                                                  let i :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      26
                                                                                                                                                                      1)
                                                                                                                                                                  let imm4 :=
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
                                                                                                                                                                  (decode_aarch32_instrs_MOV_i_T3enc_A_txt
                                                                                                                                                                    i
                                                                                                                                                                    imm4
                                                                                                                                                                    imm3
                                                                                                                                                                    Rd
                                                                                                                                                                    imm8)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__152 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             21)) == (0b11101010010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             19
                                                                                                                                                                             15)) == (0b11110#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__151 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__151 <b 3017) : Bool))))
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
                                                                                                                                                                      writeReg SEE 3017
                                                                                                                                                                      let S :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          20
                                                                                                                                                                          1)
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
                                                                                                                                                                          (decode_aarch32_instrs_MOV_r_T3enc_A_txt
                                                                                                                                                                            S
                                                                                                                                                                            imm3
                                                                                                                                                                            Rd
                                                                                                                                                                            imm2
                                                                                                                                                                            stype
                                                                                                                                                                            Rm))
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__154 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 23)) == (0b111110100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   15
                                                                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   7
                                                                                                                                                                                   4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__153 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__153 <b 3020) : Bool))))
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
                                                                                                                                                                          writeReg SEE 3020
                                                                                                                                                                          let stype :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              21
                                                                                                                                                                              2)
                                                                                                                                                                          let S :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              20
                                                                                                                                                                              1)
                                                                                                                                                                          let Rm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              4)
                                                                                                                                                                          let Rd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              8
                                                                                                                                                                              4)
                                                                                                                                                                          let Rs :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              4)
                                                                                                                                                                          (decode_aarch32_instrs_MOV_rr_T2enc_A_txt
                                                                                                                                                                            stype
                                                                                                                                                                            S
                                                                                                                                                                            Rm
                                                                                                                                                                            Rd
                                                                                                                                                                            Rs)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__156 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       25
                                                                                                                                                                                       20)) == (0b101100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       15
                                                                                                                                                                                       15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__155 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__155 <b 3022) : Bool))))
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
                                                                                                                                                                              writeReg SEE 3022
                                                                                                                                                                              let i :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  26
                                                                                                                                                                                  1)
                                                                                                                                                                              let imm4 :=
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
                                                                                                                                                                              (decode_aarch32_instrs_MOVT_T1enc_A_txt
                                                                                                                                                                                i
                                                                                                                                                                                imm4
                                                                                                                                                                                imm3
                                                                                                                                                                                Rd
                                                                                                                                                                                imm8)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__158 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         24)) == (0xEE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           20
                                                                                                                                                                                           20)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             11
                                                                                                                                                                                             9)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             4
                                                                                                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__157 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__157 <b 3024) : Bool))))
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
                                                                                                                                                                                  writeReg SEE 3024
                                                                                                                                                                                  let opc1 :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      21
                                                                                                                                                                                      3)
                                                                                                                                                                                  let CRn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      12
                                                                                                                                                                                      4)
                                                                                                                                                                                  let coproc :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      8
                                                                                                                                                                                      1)
                                                                                                                                                                                  let opc2 :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      3)
                                                                                                                                                                                  let CRm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      4)
                                                                                                                                                                                  (decode_aarch32_instrs_MRC_T1enc_A_txt
                                                                                                                                                                                    opc1
                                                                                                                                                                                    CRn
                                                                                                                                                                                    Rt
                                                                                                                                                                                    coproc
                                                                                                                                                                                    opc2
                                                                                                                                                                                    CRm)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__160 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             20)) == (0xEC5#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             11
                                                                                                                                                                                             9)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__159 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__159 <b 3026) : Bool))))
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
                                                                                                                                                                                      writeReg SEE 3026
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
                                                                                                                                                                                      let coproc :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          8
                                                                                                                                                                                          1)
                                                                                                                                                                                      let opc1 :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          4
                                                                                                                                                                                          4)
                                                                                                                                                                                      let CRm :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          4)
                                                                                                                                                                                      (decode_aarch32_instrs_MRRC_T1enc_A_txt
                                                                                                                                                                                        Rt2
                                                                                                                                                                                        Rt
                                                                                                                                                                                        coproc
                                                                                                                                                                                        opc1
                                                                                                                                                                                        CRm)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
