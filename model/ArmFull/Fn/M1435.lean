import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1049
import ArmFull.Fn.M1050
import ArmFull.Fn.M1051
import ArmFull.Fn.M1144
import ArmFull.Fn.M1145
import ArmFull.Fn.M1286
import ArmFull.Fn.M1287

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
def __DecodeA32_Unconditional__seg2 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__117 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 11 8)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        let w__116 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__116 <b 3467) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__117 : Bool)
  then
    (do
      writeReg SEE 3467
      let D := (BitVec.slice __opcode 22 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let size := (BitVec.slice __opcode 10 2)
      let index_align := (BitVec.slice __opcode 4 4)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VLD2_1_A2enc_A_txt D Rn Vd size index_align Rm)
      (pure false))
  else
    (do
      let w__119 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 11 8)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__118 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__118 <b 3468) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__119 : Bool)
      then
        (do
          writeReg SEE 3468
          let D := (BitVec.slice __opcode 22 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let size := (BitVec.slice __opcode 10 2)
          let index_align := (BitVec.slice __opcode 4 4)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VLD2_1_A3enc_A_txt D Rn Vd size index_align Rm)
          (pure false))
      else
        (do
          let w__121 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 11 8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                let w__120 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__120 <b 3472) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__121 : Bool)
          then
            (do
              writeReg SEE 3472
              let D := (BitVec.slice __opcode 22 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Vd := (BitVec.slice __opcode 12 4)
              let size := (BitVec.slice __opcode 6 2)
              let T := (BitVec.slice __opcode 5 1)
              let a := (BitVec.slice __opcode 4 1)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VLD2_a_A1enc_A_txt D Rn Vd size T a Rm)
              (pure false))
          else
            (do
              let w__123 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 11 9)) == (0b100#3 : (BitVec 3))))) : Bool) : Bool)
                then
                  (do
                    let w__122 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__122 <b 3474) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__123 : Bool)
              then
                (do
                  writeReg SEE 3474
                  let D := (BitVec.slice __opcode 22 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let itype := (BitVec.slice __opcode 8 4)
                  let size := (BitVec.slice __opcode 6 2)
                  let align := (BitVec.slice __opcode 4 2)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VLD2_m_A1enc_A_txt D Rn Vd itype size align Rm)
                  (pure false))
              else
                (do
                  let w__125 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                    then
                      (do
                        let w__124 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__124 <b 3475) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__125 : Bool)
                  then
                    (do
                      writeReg SEE 3475
                      let D := (BitVec.slice __opcode 22 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let itype := (BitVec.slice __opcode 8 4)
                      let size := (BitVec.slice __opcode 6 2)
                      let align := (BitVec.slice __opcode 4 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VLD2_m_A2enc_A_txt D Rn Vd itype size align Rm)
                      (pure false))
                  else
                    (do
                      let w__127 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                        then
                          (do
                            let w__126 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__126 <b 3478) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__127 : Bool)
                      then
                        (do
                          writeReg SEE 3478
                          let D := (BitVec.slice __opcode 22 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let size := (BitVec.slice __opcode 10 2)
                          let index_align := (BitVec.slice __opcode 4 4)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VLD3_1_A1enc_A_txt D Rn Vd size index_align Rm)
                          (pure false))
                      else
                        (do
                          let w__129 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                            then
                              (do
                                let w__128 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__128 <b 3479) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__129 : Bool)
                          then
                            (do
                              writeReg SEE 3479
                              let D := (BitVec.slice __opcode 22 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let size := (BitVec.slice __opcode 10 2)
                              let index_align := (BitVec.slice __opcode 4 4)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VLD3_1_A2enc_A_txt D Rn Vd size index_align Rm)
                              (pure false))
                          else
                            (do
                              let w__131 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__130 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__130 <b 3480) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__131 : Bool)
                              then
                                (do
                                  writeReg SEE 3480
                                  let D := (BitVec.slice __opcode 22 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let size := (BitVec.slice __opcode 10 2)
                                  let index_align := (BitVec.slice __opcode 4 4)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VLD3_1_A3enc_A_txt D Rn Vd size index_align
                                    Rm)
                                  (pure false))
                              else
                                (do
                                  let w__133 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 11 8)) == (0xE#4 : (BitVec 4))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__132 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__132 <b 3484) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__133 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3484
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let size := (BitVec.slice __opcode 6 2)
                                      let T := (BitVec.slice __opcode 5 1)
                                      let a := (BitVec.slice __opcode 4 1)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VLD3_a_A1enc_A_txt D Rn Vd size T a Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__135 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 11 9)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__134 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__134 <b 3486) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__135 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3486
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let itype := (BitVec.slice __opcode 8 4)
                                          let size := (BitVec.slice __opcode 6 2)
                                          let align := (BitVec.slice __opcode 4 2)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VLD3_m_A1enc_A_txt D Rn Vd itype
                                            size align Rm)
                                          (pure false))
                                      else
                                        (do
                                          let w__137 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__136 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__136 <b 3488) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__137 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3488
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let size := (BitVec.slice __opcode 10 2)
                                              let index_align := (BitVec.slice __opcode 4 4)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VLD4_1_A1enc_A_txt D Rn Vd size
                                                index_align Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__139 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 11 8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__138 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__138 <b 3489) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__139 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3489
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let size := (BitVec.slice __opcode 10 2)
                                                  let index_align := (BitVec.slice __opcode 4 4)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VLD4_1_A2enc_A_txt D Rn Vd
                                                    size index_align Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__141 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 11 8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__140 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__140 <b 3490) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__141 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3490
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let size := (BitVec.slice __opcode 10 2)
                                                      let index_align := (BitVec.slice __opcode 4 4)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VLD4_1_A3enc_A_txt D Rn
                                                        Vd size index_align Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__143 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 11 8)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__142 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__142 <b 3494) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__143 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3494
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let size := (BitVec.slice __opcode 6 2)
                                                          let T := (BitVec.slice __opcode 5 1)
                                                          let a := (BitVec.slice __opcode 4 1)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VLD4_a_A1enc_A_txt
                                                            D Rn Vd size T a Rm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__145 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 11 9)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__144 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__144 <b 3496) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__145 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3496
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let itype :=
                                                                (BitVec.slice __opcode 8 4)
                                                              let size :=
                                                                (BitVec.slice __opcode 6 2)
                                                              let align :=
                                                                (BitVec.slice __opcode 4 2)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VLD4_m_A1enc_A_txt
                                                                D Rn Vd itype size align Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__147 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 11 8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__146 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__146 <b 3504) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__147 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3504
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let op :=
                                                                    (BitVec.slice __opcode 21 1)
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 20 1)
                                                                  let Vn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 7 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 6 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VMAX_f_A1enc_A_txt
                                                                    D op sz Vn Vd N Q M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__149 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                             __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 23 23)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__148 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__148 <b 3506) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__149 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3506
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
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 6 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let op :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VMAX_i_A1enc_A_txt
                                                                        U D size Vn Vd N Q M op Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__151 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__150 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__150 <b 3508) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__151 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3508
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
                                                                          (decode_aarch32_instrs_VMLA_f_A1enc_A_txt
                                                                            D op sz Vn Vd N Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__153 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 23
                                                                                       23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         8)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__152 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__152 <b 3512) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__153 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3512
                                                                              let op :=
                                                                                (BitVec.slice
                                                                                  __opcode 24 1)
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
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VMLA_i_A1enc_A_txt
                                                                                op D size Vn Vd N Q
                                                                                M Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__155 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               8 8)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__154 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__154 <b 3513) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__155 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3513
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 24 1)
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
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 9 1)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VMLA_i_A2enc_A_txt
                                                                                    U D size Vn Vd
                                                                                    op N M Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__157 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   9
                                                                                                   9)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     6
                                                                                                     6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__156 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__156 <b 3516) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__157 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3516
                                                                                      let Q :=
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
                                                                                          10 1)
                                                                                      let F :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          1)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VMLA_s_A1enc_A_txt
                                                                                        Q D size Vn
                                                                                        Vd op F N M
                                                                                        Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__159 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   23
                                                                                                   23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       9
                                                                                                       8)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         6
                                                                                                         6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__158 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__158 <b 3517) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__159 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3517
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
                                                                                              10 1)
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
                                                                                          (decode_aarch32_instrs_VMLA_s_A2enc_A_txt
                                                                                            U D size
                                                                                            Vn Vd op
                                                                                            N M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__161 ← (( do
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
                                                                                                             7)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             5
                                                                                                             4)) == (0b01#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__160 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__160 <b 3526) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__161 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3526
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
                                                                                              let op :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  1)
                                                                                              let imm4 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VMOV_i_A1enc_A_txt
                                                                                                i D
                                                                                                imm3
                                                                                                Vd
                                                                                                cmode
                                                                                                Q op
                                                                                                imm4)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__163 ← (( do
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
                                                                                                                 7)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 5
                                                                                                                 4)) == (0b01#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__162 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__162 <b 3528) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__163 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3528
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
                                                                                                  let op :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      1)
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VMOV_i_A3enc_A_txt
                                                                                                    i
                                                                                                    D
                                                                                                    imm3
                                                                                                    Vd
                                                                                                    cmode
                                                                                                    Q
                                                                                                    op
                                                                                                    imm4)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__165 ← (( do
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
                                                                                                                   10)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     7
                                                                                                                     7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     5
                                                                                                                     4)) == (0b01#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__164 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__164 <b 3529) : Bool))))
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
                                                                                                      writeReg SEE 3529
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
                                                                                                      let op :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          1)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VMOV_i_A4enc_A_txt
                                                                                                        i
                                                                                                        D
                                                                                                        imm3
                                                                                                        Vd
                                                                                                        cmode
                                                                                                        Q
                                                                                                        op
                                                                                                        imm4)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__167 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   23
                                                                                                                   23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       7)) == (0b11100#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       5
                                                                                                                       4)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__166 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__166 <b 3530) : Bool))))
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
                                                                                                          writeReg SEE 3530
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
                                                                                                          let op :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VMOV_i_A5enc_A_txt
                                                                                                            i
                                                                                                            D
                                                                                                            imm3
                                                                                                            Vd
                                                                                                            cmode
                                                                                                            Q
                                                                                                            op
                                                                                                            imm4)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__169 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       23
                                                                                                                       23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         18
                                                                                                                         16)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           6)) == (0b101000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__168 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__168 <b 3536) : Bool))))
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
                                                                                                              writeReg SEE 3536
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  24
                                                                                                                  1)
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let imm3H :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  19
                                                                                                                  3)
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
                                                                                                              (decode_aarch32_instrs_VMOVL_A1enc_A_txt
                                                                                                                U
                                                                                                                D
                                                                                                                imm3H
                                                                                                                Vd
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__171 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             17
                                                                                                                             16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               6)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__170 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__170 <b 3538) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__171 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3538
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
                                                                                                                  (decode_aarch32_instrs_VMOVN_A1enc_A_txt
                                                                                                                    D
                                                                                                                    size
                                                                                                                    Vd
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__173 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 11
                                                                                                                                 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__172 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__172 <b 3552) : Bool))))
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
                                                                                                                      writeReg SEE 3552
                                                                                                                      let D :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let sz :=
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
                                                                                                                      (decode_aarch32_instrs_VMUL_f_A1enc_A_txt
                                                                                                                        D
                                                                                                                        sz
                                                                                                                        Vn
                                                                                                                        Vd
                                                                                                                        N
                                                                                                                        Q
                                                                                                                        M
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__175 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   23
                                                                                                                                   23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     8)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     4
                                                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__174 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__174 <b 3556) : Bool))))
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
                                                                                                                          writeReg SEE 3556
                                                                                                                          let op :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              24
                                                                                                                              1)
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let size :=
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
                                                                                                                          (decode_aarch32_instrs_VMUL_i_A1enc_A_txt
                                                                                                                            op
                                                                                                                            D
                                                                                                                            size
                                                                                                                            Vn
                                                                                                                            Vd
                                                                                                                            N
                                                                                                                            Q
                                                                                                                            M
                                                                                                                            Vm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (pure true))))))))))))))))))))))))))))))


end ArmFull.Functions
