import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0230
import ArmFull.Fn.M0838
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
def __DecodeA32_DataProMisc__seg1 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__98 ← (( do
    if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0x1#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
               __opcode 22 16)) == (0b1001111#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 7 4)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__96 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__96 <b 2937) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__98 : Bool)
  then
    (do
      writeReg SEE 2937
      let cond := (BitVec.slice __opcode 28 4)
      let U := (BitVec.slice __opcode 23 1)
      let Rt := (BitVec.slice __opcode 12 4)
      let imm4H := (BitVec.slice __opcode 8 4)
      let imm4L := (BitVec.slice __opcode 0 4)
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 24)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 __opcode 21)])) != 0#1)) : Bool)
      then sailThrow ((Error_ConstrainedUnpredictable ()))
      else
        (do
          (decode_aarch32_instrs_LDRD_l_A1enc_A_txt cond U Rt imm4H imm4L))
      (pure false))
  else
    (do
      let w__101 ← (( do
        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                     __opcode 11 4)) == (0x0D#8 : (BitVec 8)))))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__99 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__99 <b 2939) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__101 : Bool)
      then
        (do
          writeReg SEE 2939
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
              (decode_aarch32_instrs_LDRD_r_A1enc_A_txt cond P U W Rn Rt Rm))
          (pure false))
      else
        (do
          let w__104 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x19#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                     __opcode 11 0)) == (0xF9F#12 : (BitVec 12)))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__102 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__102 <b 2940) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__104 : Bool)
          then
            (do
              writeReg SEE 2940
              let cond := (BitVec.slice __opcode 28 4)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 3)])) != 1#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_LDREX_A1enc_A_txt cond Rn Rt))
              (pure false))
          else
            (do
              let w__107 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x1D#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                         __opcode 11 0)) == (0xF9F#12 : (BitVec 12)))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__105 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__105 <b 2942) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__107 : Bool)
              then
                (do
                  writeReg SEE 2942
                  let cond := (BitVec.slice __opcode 28 4)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 3)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_LDREXB_A1enc_A_txt cond Rn Rt))
                  (pure false))
              else
                (do
                  let w__110 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x1B#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                             __opcode 11 0)) == (0xF9F#12 : (BitVec 12)))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__108 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__108 <b 2944) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__110 : Bool)
                  then
                    (do
                      writeReg SEE 2944
                      let cond := (BitVec.slice __opcode 28 4)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rt := (BitVec.slice __opcode 12 4)
                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 3)])) != 1#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_LDREXD_A1enc_A_txt cond Rn Rt))
                      (pure false))
                  else
                    (do
                      let w__113 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27
                                 20)) == (0x1F#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                 __opcode 11 0)) == (0xF9F#12 : (BitVec 12)))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__111 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__111 <b 2946) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__113 : Bool)
                      then
                        (do
                          writeReg SEE 2946
                          let cond := (BitVec.slice __opcode 28 4)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 3)])) != 1#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_LDREXH_A1enc_A_txt cond Rn Rt))
                          (pure false))
                      else
                        (do
                          let w__116 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 7 4)) == (0xB#4 : (BitVec 4)))))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__114 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__114 <b 2948) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__116 : Bool)
                          then
                            (do
                              writeReg SEE 2948
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let imm4H := (BitVec.slice __opcode 8 4)
                              let imm4L := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_LDRH_i_A1enc_A_txt cond P U W Rn Rt imm4H imm4L)
                              (pure false))
                          else
                            (do
                              let w__119 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                             __opcode 20 16)) == (0b11111#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 7 4)) == (0xB#4 : (BitVec 4)))))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__117 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__117 <b 2952) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__119 : Bool)
                              then
                                (do
                                  writeReg SEE 2952
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let P := (BitVec.slice __opcode 24 1)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let W := (BitVec.slice __opcode 21 1)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let imm4H := (BitVec.slice __opcode 8 4)
                                  let imm4L := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_LDRH_l_A1enc_A_txt cond P U W Rt imm4H
                                    imm4L)
                                  (pure false))
                              else
                                (do
                                  let w__122 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 11 4)) == (0x0B#8 : (BitVec 8)))))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__120 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__120 <b 2954) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__122 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2954
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let P := (BitVec.slice __opcode 24 1)
                                      let U := (BitVec.slice __opcode 23 1)
                                      let W := (BitVec.slice __opcode 21 1)
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
                                          (decode_aarch32_instrs_LDRH_r_A1enc_A_txt cond P U W Rn Rt
                                            Rm))
                                      (pure false))
                                  else
                                    (do
                                      let w__125 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 22 20)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 7 4)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__123 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__123 <b 2957) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__125 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2957
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let U := (BitVec.slice __opcode 23 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rt := (BitVec.slice __opcode 12 4)
                                          let imm4H := (BitVec.slice __opcode 8 4)
                                          let imm4L := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_LDRHT_A1enc_A_txt cond U Rn Rt
                                            imm4H imm4L)
                                          (pure false))
                                      else
                                        (do
                                          let w__128 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 22 20)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                       __opcode 11 4)) == (0x0B#8 : (BitVec 8))))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__126 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__126 <b 2958) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__128 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2958
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
                                                  (decode_aarch32_instrs_LDRHT_A2enc_A_txt cond U Rn
                                                    Rt Rm))
                                              (pure false))
                                          else
                                            (do
                                              let w__131 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 7 4)) == (0xD#4 : (BitVec 4)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__129 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__129 <b 2971) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__131 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2971
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let P := (BitVec.slice __opcode 24 1)
                                                  let U := (BitVec.slice __opcode 23 1)
                                                  let W := (BitVec.slice __opcode 21 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Rt := (BitVec.slice __opcode 12 4)
                                                  let imm4H := (BitVec.slice __opcode 8 4)
                                                  let imm4L := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_LDRSB_i_A1enc_A_txt cond P
                                                    U W Rn Rt imm4H imm4L)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__134 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                 __opcode 20 16)) == (0b11111#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 7 4)) == (0xD#4 : (BitVec 4)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__132 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__132 <b 2974) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__134 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2974
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let P := (BitVec.slice __opcode 24 1)
                                                      let U := (BitVec.slice __opcode 23 1)
                                                      let W := (BitVec.slice __opcode 21 1)
                                                      let Rt := (BitVec.slice __opcode 12 4)
                                                      let imm4H := (BitVec.slice __opcode 8 4)
                                                      let imm4L := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_LDRSB_l_A1enc_A_txt
                                                        cond P U W Rt imm4H imm4L)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__137 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 11 4)) == (0x0D#8 : (BitVec 8)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__135 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__135 <b 2976) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__137 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2976
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let P := (BitVec.slice __opcode 24 1)
                                                          let U := (BitVec.slice __opcode 23 1)
                                                          let W := (BitVec.slice __opcode 21 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rt := (BitVec.slice __opcode 12 4)
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
                                                              (decode_aarch32_instrs_LDRSB_r_A1enc_A_txt
                                                                cond P U W Rn Rt Rm))
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__140 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 22 20)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 7 4)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__138 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__138 <b 2979) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__140 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2979
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              let U := (BitVec.slice __opcode 23 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Rt := (BitVec.slice __opcode 12 4)
                                                              let imm4H :=
                                                                (BitVec.slice __opcode 8 4)
                                                              let imm4L :=
                                                                (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_LDRSBT_A1enc_A_txt
                                                                cond U Rn Rt imm4H imm4L)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__143 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 22 20)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                           __opcode 11 4)) == (0x0D#8 : (BitVec 8))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__141 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__141 <b 2980) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__143 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2980
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
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
                                                                      (decode_aarch32_instrs_LDRSBT_A2enc_A_txt
                                                                        cond U Rn Rt Rm))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__146 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 7 4)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__144 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__144 <b 2982) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__146 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2982
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let P :=
                                                                        (BitVec.slice __opcode 24 1)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 23 1)
                                                                      let W :=
                                                                        (BitVec.slice __opcode 21 1)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let imm4H :=
                                                                        (BitVec.slice __opcode 8 4)
                                                                      let imm4L :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_LDRSH_i_A1enc_A_txt
                                                                        cond P U W Rn Rt imm4H imm4L)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__149 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                     __opcode 20 16)) == (0b11111#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 7 4)) == (0xF#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__147 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__147 <b 2985) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__149 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2985
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let P :=
                                                                            (BitVec.slice __opcode
                                                                              24 1)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              23 1)
                                                                          let W :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let imm4H :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          let imm4L :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_LDRSH_l_A1enc_A_txt
                                                                            cond P U W Rt imm4H
                                                                            imm4L)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__152 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 27 25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 22
                                                                                       22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 20
                                                                                         20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         4)) == (0x0F#8 : (BitVec 8)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__150 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__150 <b 2987) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__152 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2987
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let P :=
                                                                                (BitVec.slice
                                                                                  __opcode 24 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 1)
                                                                              let W :=
                                                                                (BitVec.slice
                                                                                  __opcode 21 1)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 11)])) != 0#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_LDRSH_r_A1enc_A_txt
                                                                                    cond P U W Rn Rt
                                                                                    Rm))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__155 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 27
                                                                                         24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           22 20)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           7 4)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__153 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__153 <b 2990) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__155 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2990
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let imm4H :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let imm4L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_LDRSHT_A1enc_A_txt
                                                                                    cond U Rn Rt
                                                                                    imm4H imm4L)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__158 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 24)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               22 20)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 4)) == (0x0F#8 : (BitVec 8))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__156 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__156 <b 2991) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__158 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2991
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
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
                                                                                          (decode_aarch32_instrs_LDRSHT_A2enc_A_txt
                                                                                            cond U
                                                                                            Rn Rt Rm))
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__161 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 21)) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
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
                                                                                                let w__159 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__159 <b 3005) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__161 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3005
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 1)
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Ra :=
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
                                                                                          (decode_aarch32_instrs_MLA_A1enc_A_txt
                                                                                            cond S
                                                                                            Rd Ra Rm
                                                                                            Rn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__164 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     27
                                                                                                     20)) == (0x06#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
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
                                                                                                    let w__162 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__162 <b 3007) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__164 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3007
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
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_MLS_A1enc_A_txt
                                                                                                cond
                                                                                                Rd
                                                                                                Ra
                                                                                                Rm
                                                                                                Rn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__167 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         27
                                                                                                         21)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         19
                                                                                                         16)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__165 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__165 <b 3009) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__167 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3009
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
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let imm12 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      12)
                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             19)])) != 0#1)) : Bool)
                                                                                                  then
                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                      ()))
                                                                                                  else
                                                                                                    (do
                                                                                                      (decode_aarch32_instrs_MOV_i_A1enc_A_txt
                                                                                                        cond
                                                                                                        S
                                                                                                        Rd
                                                                                                        imm12))
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__170 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           27
                                                                                                           20)) == (0x30#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                               __opcode
                                                                                                               28
                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__168 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__168 <b 3010) : Bool))))
                                                                                                        else
                                                                                                          (pure false))
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
                                                                                                      writeReg SEE 3010
                                                                                                      let cond :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          4)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let imm12 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          12)
                                                                                                      (decode_aarch32_instrs_MOV_i_A2enc_A_txt
                                                                                                        cond
                                                                                                        imm4
                                                                                                        Rd
                                                                                                        imm12)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__173 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 27
                                                                                                                 21)) == (0b0001101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   19
                                                                                                                   16)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
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
                                                                                                                let w__171 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__171 <b 3014) : Bool))))
                                                                                                            else
                                                                                                              (pure false))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__173 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3014
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
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let imm5 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              5)
                                                                                                          let stype :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              2)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     19)])) != 0#1)) : Bool)
                                                                                                          then
                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                              ()))
                                                                                                          else
                                                                                                            (do
                                                                                                              (decode_aarch32_instrs_MOV_r_A1enc_A_txt
                                                                                                                cond
                                                                                                                S
                                                                                                                Rd
                                                                                                                imm5
                                                                                                                stype
                                                                                                                Rm))
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__176 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     27
                                                                                                                     21)) == (0b0001101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       19
                                                                                                                       16)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         7
                                                                                                                         7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                       __opcode
                                                                                                                       28
                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__174 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__174 <b 3018) : Bool))))
                                                                                                                else
                                                                                                                  (pure false))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__176 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3018
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
                                                                                                              let Rd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let Rs :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              let stype :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  2)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         19)])) != 0#1)) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_aarch32_instrs_MOV_rr_A1enc_A_txt
                                                                                                                    cond
                                                                                                                    S
                                                                                                                    Rd
                                                                                                                    Rs
                                                                                                                    stype
                                                                                                                    Rm))
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (pure true)))))))))))))))))))))))))))


end ArmFull.Functions
